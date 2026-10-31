"""Tests of scripts/review_site.py: the commands of the standard review (`standard`, `hash`, `guide`, `post`) and the
commands beside them. The review site is faked by patching `review_site.get` (its data) and `review_site.fetch` (a text
file of GitHub's), and GitHub by patching `review_site.gh`: nothing here touches the network or GitHub.

`IntakeReadsPostTests` feeds what `post --dry-run` writes to the review site's own parser (its
scripts/standard_intake.py), so that the two never drift. It needs the site's repository, at $TAUCETI_REVIEW_SITE_DIR or
beside this one, and the packages that repository runs on (evidence-core and evidence-store: its .venv has them), and
skips without them.

Run them from the root of the repository: python3 -m unittest discover -s tests
"""
import contextlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import types
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "scripts"))
import review_site  # noqa: E402

#: The vector of the site's tests/test_standard.py, which pins the two copies of `version_of` equal: CRLF line ends,
#: trailing spaces, blank lines at both ends.
VECTOR = ("\n## What it says\r\n`triple n` is $3n$.  \r\n\r\n## References and tests\n- Fixture documentation.\n\n"
          "## Lean subtleties\nNone.\n\n")
COMMIT = "0123456789abcdef0123456789abcdef01234567"
AGENT = "Voyager, claude-fable-5-1, session 7"
MARK = "<!-- agent: tool=Voyager; model=claude-fable-5-1; session=7 -->"
NOTE = "Reviews of declarations checked at Tau Ceti 0123456789ab."
HEAD = MARK + "\n" + NOTE + "\n"
AXES = ["object", "convention", "edge-cases", "junk", "vacuous", "choice", "generality", "naming"]
CELLS = {**dict.fromkeys(AXES, "checked"), "choice": "na"}
CELLS_LINE = "object, convention, edge-cases, junk, vacuous, choice n/a, generality, naming"


def V(text):
    return review_site.version_of(text)


def review(says="`Fixture.a n` is $n$.", refs=("- Fixture documentation, §1.",), subtle="None."):
    """A standard review's text, in its three parts."""
    parts = ["## What it says", says, "", "## References and tests", *refs, "", "## Lean subtleties", subtle]
    return "\n".join(parts) + "\n"


#: Texts with fences and lines like commands in them, and whether the intake reads a block of each back whole: it
#: closes a block at the last `~~~` line before the next command line, so a command line after a `~~~` line of the text
#: ends the block there; and it does not close a block that holds a `~~~review` line before its first `~~~` line.
BLOCKS = {
    "a fence of backticks": (review(says="```lean\ndef x := 1\n```"), True),
    "a fence of tildes": (review(says="a fence of tildes:\n~~~lean\ndef x := 1\n~~~\nand more"), True),
    "a command line before any tilde line": (
        review(says="Test: a command line before any `~~~` line is text\n```lean\ndef x := 1\n```"), True),
    "a command line after a tilde line": (
        review(says="a fence of tildes:\n~~~lean\ndef x := 1\n~~~\nTest: the next command line\nand more"), False),
    "an indented command line after a tilde line": (
        review(says="~~~lean\ndef x := 1\n~~~\n   Edit: Fixture.c — dd83c85a — the next command"), False),
    "a ~~~review line": (review(says="~~~review\nnested\n~~~"), False),
    "a ~~~review line after a tilde line": (review(says="~~~lean\nx\n~~~\n~~~review\nnested\n~~~"), True),
    "a line separator that makes a command line": (review(says="x\u2028~~~\u2028Test: y\u2028z"), False),
}


def long_review(n):
    """A review of about 3,000 characters."""
    return review(says="\n".join(f"line {n:02d} " + "x" * 52 for _ in range(48)))


def chunk(decl, text):
    """The lines of a Write of ``text`` to ``decl``, as `post` writes them: what a comment holds for it."""
    return f"Write: {decl} — {CELLS_LINE}\n~~~review\n{review_site.normalize(text)}\n~~~\n"


def approve(decl, version, cells=CELLS):
    return {"approve": decl, "version": version, "cells": cells}


def write(decl, text, cells=CELLS):
    return {"write": decl, "cells": cells, "text": text}


def edit(decl, parent, text, note, dropped=(), cells=CELLS):
    return {"edit": decl, "parent": parent, "cells": cells, "note": note, "dropped": list(dropped), "text": text}


def person(label="Chris Birkbeck"):
    return {"kind": "person", "login": "cb", "agent": None, "label": label, "involvement": "unknown"}


def agent(tool="Voyager", model="claude-fable-5-1"):
    return {"kind": "agent", "login": "cb", "agent": {"tool": tool, "model": model}, "label": f"{tool} ({model})",
            "involvement": "unknown"}


def view(by, at, verdict="accept", text="", **more):
    """A record view of a declaration, as the site's pages list it (evidence-core's `record_view`)."""
    return {"id": f"r-{at}-{by['label']}", "kind": "review", "verdict": verdict, "by": by, "at": at, "text": text,
            "state": "stands" if verdict == "accept" else "open", "inForce": True, "applies": True,
            "url": "https://github.com/o/r/issues/1#issuecomment-5", **more}


def entry(text, version=None, by=None, at="2026-10-26T10:00:00Z", approvers=(), earlier=0, current=True):
    """A declaration's entry in its shard of standard/<k>.json."""
    return {"text": text, "version": version or V(text), "at": at, "by": by or agent("Claude Code", "claude-opus-5-5"),
            "approving": True, "url": "https://github.com/o/r/issues/1#issuecomment-901", "current": current,
            "approvers": list(approvers), "earlier": earlier}


def approver(by, at, checked=CELLS):
    return {"by": by, "at": at, "checked": checked, "url": "https://github.com/o/r/issues/1#issuecomment-902"}


def parse_writes(body):
    """The (declaration, text) of each Write in a comment, from the block each has: a `~~~review` line, the text, and
    the last `~~~` line before the next Write or the end of the comment."""
    lines, out, k = body.rstrip("\n").split("\n"), [], 0
    while k < len(lines):
        m = re.match(r"^Write: (\S+) — ", lines[k])
        if m is None:
            k += 1
            continue
        assert lines[k + 1] == "~~~review", lines[k + 1]
        end = next(j for j in range(k + 2, len(lines))
                   if lines[j] == "~~~" and (j + 1 == len(lines) or lines[j + 1].startswith("Write: ")))
        out.append((m[1], "\n".join(lines[k + 2:end])))
        k = end + 1
    return out


class Site:
    """The data the review site publishes, as `review_site.get` reads it: a few declarations, each with its record
    views, and the standard reviews the site shows. The library has one module, `Fixture`; a declaration outside it
    may be in a module of its own (modules.json lists them). ``outside`` is the packages whose declarations the site
    asks its question of (`meta.review.outside`), or None for a site that does not say. ``reads`` lists what was asked
    of it."""
    NODES, NAMES, STANDARD = 4, 4, 256

    def __init__(self, commit=COMMIT, standard=True, bulk=1, outside=("Mathlib",)):
        self.commit, self.standard, self.bulk, self.outside = commit, standard, bulk, outside
        self.decls, self.reviews, self.modules, self.reads = [], {}, ["Fixture"], []

    def add(self, name, review=None, records=(), project=True, module=None):
        if module and module not in self.modules:
            self.modules.append(module)
        self.decls.append((name, project, list(records), module))
        if review:
            self.reviews[name] = review
        return self

    def get(self, path):
        self.reads.append(path)
        shards = {"nodes": self.NODES, "names": self.NAMES, **({"standard": self.STANDARD} if self.standard else {})}
        if path == "meta.json":
            return {"library": {"commit": self.commit}, "shards": shards, "store": {"bulk": self.bulk},
                    **({} if self.outside is None else {"review": {"outside": list(self.outside)}})}
        if path == "modules.json":
            return [[module, "pkg", "", ""] for module in self.modules]
        if path == "upstream.json":
            return {name: {"records": records} for name, project, records, _ in self.decls if not project}
        kind, _, rest = path.partition("/")
        k = int(rest.removesuffix(".json")) if rest else -1
        if kind == "names":
            return [[i, name] for i, (name, _, _, _) in enumerate(self.decls) if review_site.fnv(name, self.NAMES) == k]
        if kind == "nodes":
            return [[name, "t", 1 if project else 0, 0 if project else self.modules.index(module) if module else -1]
                    for name, project, _, module in self.decls[k * self.NODES:(k + 1) * self.NODES]]
        if kind == "m":
            return {"decls": [{"id": i, "records": records} for i, (_, project, records, _) in enumerate(self.decls)
                              if project]}
        if kind == "standard":
            return {name: r for name, r in self.reviews.items() if review_site.fnv(name, self.STANDARD) == k}
        raise AssertionError(f"the site was asked for {path}")


class Gh:
    """GitHub's `gh`: it records the comments it is asked to post, and answers with a link to each."""

    def __init__(self):
        self.calls = []

    def __call__(self, *args, body=None):
        self.calls.append((args, body))
        return f"https://github.com/{review_site.REPO}/issues/1#issuecomment-{len(self.calls)}"


class Case(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.dir)
        self.site, self.gh = Site(), Gh()
        # Whatever a test fails to fake does not reach the network or run a program.
        for module, name in ((review_site.urllib.request, "urlopen"), (review_site.subprocess, "run")):
            patcher = mock.patch.object(module, name, side_effect=AssertionError(f"unexpected call of {name}"))
            patcher.start()
            self.addCleanup(patcher.stop)

    def jsonl(self, *rows, name="actions.jsonl"):
        path = self.dir / name
        path.write_text("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows), encoding="utf-8")
        return str(path)

    def cli(self, *argv, fetch=None):
        """(exit code, stdout, stderr) of `review_site.py ARGV`, against the fake site."""
        out, err, code = io.StringIO(), io.StringIO(), 0

        def unexpected(url):
            raise AssertionError(f"unexpected fetch of {url}")

        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err), \
                mock.patch.object(review_site, "get", self.site.get), mock.patch.object(review_site, "gh", self.gh), \
                mock.patch.object(review_site, "fetch", fetch or unexpected):
            try:
                review_site.main(list(argv))
            except SystemExit as e:
                code = e.code
        return code, out.getvalue(), err.getvalue()

    def post(self, *rows, dry=True, extra=(), commit=COMMIT[:12]):
        return self.cli("post", self.jsonl(*rows), "--agent", AGENT, "--commit", commit,
                        *(["--dry-run"] if dry else []), *extra)

    def outside(self, name, module, text=None):
        """A declaration outside the library, in ``module``, with a standard review of ``text`` unless it has none."""
        self.site.add(name, entry(text) if text else None, module=module, project=False)


class VersionTests(Case):
    def test_the_shared_vector(self):
        self.assertEqual(review_site.version_of(VECTOR), "dd83c85a488e22c8")
        self.assertEqual(review_site.version_of(review_site.normalize(VECTOR)), "dd83c85a488e22c8")

    def test_normalize(self):
        norm = review_site.normalize
        self.assertEqual(norm("\r\n\r\nA  \r\nB\t\rC\n\n\n"), "A\nB\nC")
        # Blank lines inside stay, and so does an indent; a line of spaces is blank.
        self.assertEqual(norm("  A\n\n\n B \n   \nC"), "  A\n\n\n B\n\nC")
        text = "\n \n## A  \r\n x\r\r\n\n"
        self.assertEqual(norm(norm(text)), norm(text))

    def test_the_end_of_a_line_loses_all_unicode_white_space(self):
        # `line.rstrip()` strips every kind of white space, a no-break space and an ideographic one among them, where
        # a regex like `[ \t]+$` would not: the vector does not tell the two apart.
        self.assertEqual(review_site.version_of("a\u00a0\u3000\nb\u2003"), review_site.version_of("a\nb"))
        self.assertNotEqual(review_site.version_of("a\u00a0b"), review_site.version_of("a b"))

    def test_the_hash_command_prints_a_files_version(self):
        path = self.dir / "review.md"
        path.write_bytes(VECTOR.encode("utf-8"))  # with its CRLF line ends
        self.assertEqual(self.cli("hash", str(path)), (0, "dd83c85a488e22c8\n", ""))
        for text in ("  an indented first line  \r\n\r\n\r\n", review().replace("\n", "\r\n"), "§ℂ𝔾\n"):
            path.write_bytes(text.encode("utf-8"))
            self.assertEqual(self.cli("hash", str(path)), (0, V(text) + "\n", ""))
        code, out, err = self.cli("hash", str(self.dir / "missing.md"))
        self.assertEqual((code, out), (2, ""))
        self.assertIn("cannot read", err)


class FetchTests(unittest.TestCase):
    """`get` and `fetch`, which every other test patches, against a fake `urlopen`."""

    @staticmethod
    def answer(body):
        class Response:
            def __enter__(self):
                return self

            def __exit__(self, *exc):
                return False

            def read(self):
                return body

        return lambda url, timeout: Response()

    def get(self, body):
        with mock.patch.object(review_site.urllib.request, "urlopen", self.answer(body)):
            return review_site.get("meta.json")

    def test_get_reads_the_sites_data_past_its_cache(self):
        urls = []

        def urlopen(url, timeout):
            urls.append(url)
            return self.answer('{"library": {"commit": "ab"}, "n": "§"}'.encode("utf-8"))(url, timeout)

        with mock.patch.object(review_site.urllib.request, "urlopen", urlopen):
            self.assertEqual(review_site.get("meta.json"), {"library": {"commit": "ab"}, "n": "§"})
        self.assertRegex(urls[0], rf"^{re.escape(review_site.SITE)}data/meta\.json\?t=\d+$")

    def test_get_that_cannot_read_is_an_error(self):
        def refused(url, timeout):
            raise OSError("no route")

        for urlopen in (refused, self.answer(b"<html>not json</html>")):
            with self.subTest(urlopen=urlopen), mock.patch.object(review_site.urllib.request, "urlopen", urlopen), \
                    contextlib.redirect_stderr(io.StringIO()) as err, self.assertRaises(SystemExit) as raised:
                review_site.get("meta.json")
            self.assertEqual(raised.exception.code, 2)
            self.assertIn("cannot read", err.getvalue())

    def test_fetch_decodes_utf8_and_drops_a_byte_order_mark(self):
        for body in ("a § b".encode("utf-8"), b"\xef\xbb\xbf" + "a § b".encode("utf-8")):
            with mock.patch.object(review_site.urllib.request, "urlopen", self.answer(body)):
                self.assertEqual(review_site.fetch("https://example.org/x"), "a § b")


class ShardTests(Case):
    def test_a_names_shard_is_the_sites(self):
        # FNV-1a over UTF-16 code units, as the site's web/data.js and scripts/common.py compute it: a character
        # outside the BMP is two units.
        self.assertEqual(review_site.fnv("TauCeti.Foo.bar", 256), 111)
        self.assertEqual(review_site.fnv("TauCeti.α₁.𝔾", 256), 47)


class GuideTests(Case):
    DOC = ("# Reviewing\n\nIntro.\n\n<!-- standard-review:begin -->\n## The standard review\n\nThree parts.\n"
           "<!-- standard-review:end -->\n\n## What you need\n\nElsewhere.\n")

    def test_the_guide_is_the_marked_section(self):
        urls = []

        def fetch(url):
            urls.append(url)
            return self.DOC

        code, out, err = self.cli("guide", fetch=fetch)
        self.assertEqual((code, err), (0, ""))
        self.assertEqual(out, "## The standard review\n\nThree parts.\n")
        self.assertEqual(urls, [f"https://raw.githubusercontent.com/{review_site.REPO}/main/AI-REVIEWS.md"])

    def test_the_guide_needs_its_markers(self):
        for doc in ("# Reviewing\n\nNo markers.\n", self.DOC.replace("<!-- standard-review:end -->", ""),
                    self.DOC.replace("<!-- standard-review:begin -->", ""), self.DOC.replace("begin", "BEGIN"),
                    self.DOC.replace("begin", "x").replace("end", "begin")):
            with self.subTest(doc=doc[:60]):
                code, out, err = self.cli("guide", fetch=lambda url, doc=doc: doc)
                self.assertEqual((code, out), (2, ""))
                self.assertIn("standard-review:begin", err)

    def test_an_unreadable_guide_is_an_error(self):
        def fetch(url):
            raise OSError("no route")

        code, out, err = self.cli("guide", fetch=fetch)
        self.assertEqual((code, out), (2, ""))
        self.assertIn("no route", err)


class StandardTests(Case):
    def setUp(self):
        super().setUp()
        self.text = review()
        self.voyager = agent()
        records = [
            view(agent("Codex", "GPT-6 Astra"), "2026-10-24T09:00:00Z", text="Matches Stacks 00AB."),  # before it
            view(self.voyager, "2026-10-28T09:00:00Z", text="Also in Atiyah-Macdonald 1.8."),  # since it
            view(person(), "2026-10-29T09:00:00Z", text="A person's yes, with a reason."),
            view(agent("Codex", "GPT-6 Astra"), "2026-10-30T09:00:00Z", std="approved"),  # of the standard review
            view(agent("Claude Code", "claude-opus-5-5"), "2026-10-30T10:00:00Z", text="Withdrawn reasons.",
                 inForce=False),
            view(agent(), "2026-10-27T09:00:00Z", verdict="problem", text="The edge case n = 0 is wrong.",
                 category="edge-cases"),
            view(agent(), "2026-10-27T10:00:00Z", verdict="problem", text="Fixed already.", state="fixed"),
        ]
        self.site.add("Fixture.a", entry(self.text, approvers=[approver(self.voyager, "2026-10-27T10:00:00Z")],
                                         earlier=2), records)
        self.site.add("Fixture.b", None, [view(agent("Codex", "GPT-6 Astra"), "2026-10-25T09:00:00Z",
                                               text="A second yes."),
                                          view(agent(), "2026-10-20T09:00:00Z", text="Old, but nothing is newer.")])

    def test_standard_needs_a_site_that_shows_it(self):
        self.site.standard = False
        for argv in (("standard", "Fixture.a"), ("standard", "--json", "Fixture.a")):
            code, out, err = self.cli(*argv)
            self.assertEqual((code, out), (2, ""))
            self.assertIn("the site does not show standard reviews yet", err)

    def test_standard_prints_the_text_its_version_and_who_approved_it(self):
        code, out, err = self.cli("standard", "Fixture.a")
        self.assertEqual((code, err), (0, ""))
        for want in (f"version {V(self.text)}", "current", "Claude Code (claude-opus-5-5)",
                     "Voyager (claude-fable-5-1)", CELLS_LINE, "earlier approvals: 2"):
            self.assertIn(want, out)
        self.assertIn("~~~review\n" + self.text.strip("\n") + "\n~~~\n", out)

    def test_standard_says_when_the_text_was_written_for_an_earlier_version_of_the_declaration(self):
        self.site.reviews["Fixture.a"]["current"] = False
        self.assertIn("earlier version of the declaration", self.cli("standard", "Fixture.a")[1])

    def test_standard_prints_what_is_new_to_an_editor(self):
        out = self.cli("standard", "Fixture.a")[1]
        # The reasons of an earlier-form yes recorded since the version, and the noes still open: not the yes from
        # before the version, a person's, a record of the standard review, a withdrawn one, or a no that was fixed.
        for want in ("Also in Atiyah-Macdonald 1.8.", "The edge case n = 0 is wrong."):
            self.assertIn(want, out)
        for unwanted in ("Matches Stacks 00AB.", "A person's yes", "Withdrawn reasons.", "Fixed already."):
            self.assertNotIn(unwanted, out)

    def test_standard_json(self):
        code, out, err = self.cli("standard", "--json", "Fixture.a", "Fixture.b")
        self.assertEqual((code, err), (0, ""))
        got = json.loads(out)
        self.assertEqual(list(got), ["Fixture.a", "Fixture.b"])
        a = got["Fixture.a"]
        self.assertEqual(set(a), {"version", "text", "unfolded", "noes"})
        self.assertEqual((a["version"], a["text"]), (V(self.text), self.text))
        self.assertEqual(a["unfolded"], [{"by": "Voyager (claude-fable-5-1)", "at": "2026-10-28T09:00:00Z",
                                          "text": "Also in Atiyah-Macdonald 1.8."}])
        self.assertEqual([(n["by"], n["text"]) for n in a["noes"]],
                         [("Voyager (claude-fable-5-1)", "The edge case n = 0 is wrong.")])

    def test_without_a_version_every_yes_of_the_earlier_form_is_unfolded(self):
        got = json.loads(self.cli("standard", "--json", "Fixture.b")[1])["Fixture.b"]
        self.assertEqual((got["version"], got["text"]), (None, ""))
        self.assertEqual([u["text"] for u in got["unfolded"]], ["Old, but nothing is newer.", "A second yes."])
        self.assertEqual(got["noes"], [])
        text = self.cli("standard", "Fixture.b")[1]
        self.assertIn("no standard review yet", text)
        self.assertIn("A second yes.", text)

    def test_a_declaration_outside_the_library(self):
        text = review(says="`Int` is the integers.")
        self.site.add("Int", entry(text), [view(agent(), "2026-10-28T09:00:00Z", text="Mathlib's own.")], project=False)
        got = json.loads(self.cli("standard", "--json", "Int")[1])["Int"]
        self.assertEqual(got["version"], V(text))
        self.assertEqual([u["text"] for u in got["unfolded"]], ["Mathlib's own."])

    def test_a_name_the_site_does_not_have(self):
        code, out, err = self.cli("standard", "Fixture.a", "Fixture.nope")
        self.assertEqual(code, 1)
        self.assertIn("the site has no such declaration", out)
        self.assertIn("version", out)  # the names it has are still shown
        code, out, err = self.cli("standard", "--json", "Fixture.nope")
        self.assertEqual((code, json.loads(out)), (1, {"Fixture.nope": None}))


class PostTests(Case):
    def setUp(self):
        super().setUp()
        self.a = review(says="a")
        self.c = review(says="c", refs=("- Fixture documentation, §1.", "- `Fixture.c_one` — its value at 1"))
        self.site.add("Fixture.a", entry(self.a)).add("Fixture.b").add("Fixture.c", entry(self.c))

    def refused(self, *rows, **kw):
        """Posts for real, and checks that it was refused with nothing posted. The reasons on stderr."""
        code, out, err = self.post(*rows, dry=False, **kw)
        self.assertEqual((code, out), (1, ""), err)
        self.assertEqual(self.gh.calls, [])
        self.assertIn("refused", err)
        return err

    def test_post_formats_the_bulk_lines(self):
        b = review(says="b says this\nin two lines")
        c2 = review(says="c, with more", refs=("- Fixture documentation, §1.", "- `Fixture.c_uno` — its value at 1"))
        code, out, err = self.post(  # the cells given in no particular order
            approve("Fixture.a", V(self.a), dict(reversed(list(CELLS.items())))), write("Fixture.b", b),
            edit("Fixture.c", V(self.c), c2, "names the test by its new name",
                 [{"item": "`Fixture.c_one`", "why": "renamed `Fixture.c_uno` in Tau Ceti"}]))
        self.assertEqual((code, err.count("refused")), (0, 0))
        want = "\n".join([
            MARK, NOTE,
            f"Approve: Fixture.a — {V(self.a)} — {CELLS_LINE}",
            f"Write: Fixture.b — {CELLS_LINE}", "~~~review", b.strip("\n"), "~~~",
            f"Edit: Fixture.c — {V(self.c)} — {CELLS_LINE} — names the test by its new name",
            "Dropped: `Fixture.c_one` — renamed `Fixture.c_uno` in Tau Ceti",
            "~~~review", c2.strip("\n"), "~~~"]) + "\n"
        self.assertEqual(out, want + "\n")  # `print` ends the comment with a blank line
        self.assertEqual(self.gh.calls, [])  # a dry run posts nothing

    def test_post_posts_each_comment_with_gh(self):
        rows = [approve("Fixture.a", V(self.a)), write("Fixture.b", review())]
        dry = self.post(*rows)[1]
        code, out, err = self.post(*rows, dry=False)
        self.assertEqual(code, 0, err)
        (args, body), = self.gh.calls
        self.assertEqual(args, ("issue", "comment", "1", "-R", review_site.REPO, "--body-file", "-"))
        self.assertEqual(body + "\n", dry)
        self.assertEqual(out, f"https://github.com/{review_site.REPO}/issues/1#issuecomment-1\n")
        self.assertIn("2 actions in 1 comment", err)
        # The comment goes on the bulk issue the site names.
        self.site.bulk = 7
        self.assertEqual(self.post(*rows, dry=False)[0], 0)
        self.assertEqual(self.gh.calls[1][0][:3], ("issue", "comment", "7"))

    def test_the_note_follows_the_agent_line_in_each_comment(self):
        out = self.post(approve("Fixture.a", V(self.a)), extra=("--note", "Checked for the update\nof 2026-10-31."))[1]
        self.assertEqual(out.splitlines()[:2], [MARK, "Checked for the update of 2026-10-31."])
        for note in ("Test: this is a line the intake would read", "Approve: Fixture.a — dd83c85a — object"):
            code, out, err = self.post(approve("Fixture.a", V(self.a)), extra=("--note", note))
            self.assertEqual((code, out), (2, ""))
            self.assertIn("--note", err)

    def test_post_keeps_the_fields_of_a_line_on_it(self):
        dropped = [{"item": "`Fixture.c_one`", "why": "renamed\nin Tau Ceti,\n  and moved"}]
        note = "names the test\n  by its new name"
        out = self.post(edit("Fixture.c", V(self.c), review(says="c2"), note, dropped))[1]
        self.assertIn(f" — {CELLS_LINE} — names the test by its new name\n", out)
        self.assertIn("\nDropped: `Fixture.c_one` — renamed in Tau Ceti, and moved\n", out)

    def test_post_writes_the_text_as_its_version_is_taken(self):
        # GitHub hands a body back with CRLF line ends, an editor leaves trailing spaces and blank lines at the ends:
        # the comment holds the text normalized, which is the text the agent hashed.
        text = "\n\n" + review().replace("\n", "  \r\n") + "\n\n"
        out = self.post(write("Fixture.b", text))[1]
        self.assertNotIn("\r", out)
        block = out.split("~~~review\n")[1].split("\n~~~\n")[0]
        self.assertEqual(block, review().strip("\n"))
        self.assertEqual(V(block), V(text))

    def test_post_refuses_a_stale_version(self):
        self.site.reviews["Fixture.a"] = entry(self.a, version="a" * 16)
        self.site.reviews["Fixture.c"] = entry(self.c, version="c" * 16)
        err = self.refused(approve("Fixture.a", "b" * 16))
        self.assertIn("a" * 16, err)  # the current version is named
        err = self.refused(edit("Fixture.c", "b" * 16, review(says="c2"), "a note"))
        self.assertIn("c" * 16, err)
        # A stale approval among good ones holds back the good ones.
        self.refused(approve("Fixture.c", "c" * 16), approve("Fixture.a", "b" * 16))
        # The current version is named by its first 8 digits or more, and no fewer.
        for given, ok in (("a" * 16, True), ("a" * 8, True), ("A" * 8, True), ("a" * 7, False), ("a" * 17, False),
                          ("zzzzzzzz", False), ("", False)):
            with self.subTest(version=given):
                self.gh.calls.clear()
                code = self.post(approve("Fixture.a", given), dry=False)[0]
                self.assertEqual((code, len(self.gh.calls)), (0, 1) if ok else (1, 0))

    def test_post_refuses_a_version_when_the_site_shows_no_review(self):
        err = self.refused(approve("Fixture.b", "a" * 16))
        self.assertIn("Fixture.b", err)
        self.assertIn("no standard review", err)

    def test_post_accepts_a_drafts_version(self):
        draft = review(says="a draft of b")
        drafts = self.jsonl(write("Fixture.b", draft), edit("Fixture.c", V(self.c), review(says="c, drafted"), "n"),
                            approve("Fixture.a", V(self.a)), name="drafts.jsonl")
        self.refused(approve("Fixture.b", V(draft)))  # the site shows no review of b yet
        code, out, err = self.post(approve("Fixture.b", V(draft)), extra=("--drafts", drafts))
        self.assertEqual(code, 0, err)
        self.assertIn(f"Approve: Fixture.b — {V(draft)} — {CELLS_LINE}", out)
        # An edit may name a draft as its parent; the site's current version is still good beside the draft's.
        code, out, err = self.post(edit("Fixture.b", V(draft), review(says="b, improved"), "improves it"),
                                   approve("Fixture.c", V(self.c)), extra=("--drafts", drafts))
        self.assertEqual(code, 0, err)
        # The draft of another declaration is no version of this one, and a hash that is nowhere is none.
        self.refused(approve("Fixture.a", V(draft)), extra=("--drafts", drafts))
        self.refused(approve("Fixture.b", "f" * 16), extra=("--drafts", drafts))

    def test_post_refuses_incomplete_cells_or_parts(self):
        text = review(says="b")
        bad_cells = {
            "an axis left out": {k: v for k, v in CELLS.items() if k != "naming"},
            "no cells": {},
            "a state that is neither": {**CELLS, "junk": "unchecked"},
            "an axis that is not the rubric's": {**CELLS, "other": "checked"},
            "a state that is no word": {**CELLS, "object": True},
        }
        for why, cells in bad_cells.items():
            for action in (approve("Fixture.a", V(self.a), cells), write("Fixture.b", text, cells),
                           edit("Fixture.c", V(self.c), review(says="c2"), "n", cells=cells)):
                with self.subTest(why=why, action=next(iter(action))):
                    self.assertIn("cells", self.refused(action))
        absent = approve("Fixture.a", V(self.a))
        del absent["cells"]
        self.assertIn("cells", self.refused(absent))
        # `n/a` is as good as `na` for a check that does not apply, as in the lines the intake reads.
        code, out, err = self.post(approve("Fixture.a", V(self.a), {**CELLS, "choice": "n/a"}))
        self.assertEqual(code, 0, err)
        self.assertIn(f" — {CELLS_LINE}\n", out)
        # The three parts of the text, under their headings and in order.
        heads = ["## What it says", "## References and tests", "## Lean subtleties"]
        bad_texts = {
            "a part missing": "\n".join([heads[0], "x", "", heads[1], "- r"]),
            "the parts out of order": "\n".join([heads[1], "- r", "", heads[0], "x", "", heads[2], "None."]),
            "a heading that is not exact": review().replace("## What it says", "### What it says"),
            "a part twice": review() + "\n" + "\n".join([heads[2], "Twice."]),
            "text before the first part": "A title.\n\n" + review(),
            "a part empty": review(subtle=""),
            "no text": "",
        }
        for why, bad in bad_texts.items():
            for action in (write("Fixture.b", bad), edit("Fixture.c", V(self.c), bad, "n")):
                with self.subTest(why=why, action=next(iter(action))):
                    self.assertIn("## ", self.refused(action))
        for action in ({"write": "Fixture.b", "cells": CELLS},
                       {"edit": "Fixture.c", "parent": V(self.c), "cells": CELLS, "note": "n"}):
            self.assertIn("text", self.refused(action))  # a write or an edit without its text
        self.assertIn("note", self.refused(edit("Fixture.c", V(self.c), review(says="c2"), "  ")))

    def test_post_refuses_a_name_not_on_the_site(self):
        err = self.refused(approve("Fixture.a", V(self.a)), write("Fixture.nope", review()))
        self.assertIn("Fixture.nope", err)
        self.assertNotIn("(Fixture.a)", err)  # only the action that is wrong is named

    def test_post_takes_the_declarations_outside_the_library_that_the_site_asks_about(self):
        # Mathlib's, as the site lists its package (meta.review.outside): a module of it, or the package's own.
        foo, baz = review(says="`Nat.foo` is a successor"), review(says="`Nat.baz` is an order")
        self.outside("Nat.foo", "Mathlib.Data.Nat.Basic", foo)
        self.outside("Nat.bar", "Mathlib")
        self.outside("Nat.baz", "Mathlib.Order.Basic", baz)
        rows = [approve("Nat.foo", V(foo)), write("Nat.bar", review(says="bar")),
                edit("Nat.baz", V(baz), review(says="`Nat.baz` is a partial order"), "says which order"),
                approve("Fixture.a", V(self.a))]
        self.site.reads.clear()
        code, out, err = self.post(*rows)
        self.assertEqual(code, 0, err)
        for line in (f"Approve: Nat.foo — {V(foo)} — {CELLS_LINE}", f"Write: Nat.bar — {CELLS_LINE}",
                     f"Edit: Nat.baz — {V(baz)} — {CELLS_LINE} — says which order"):
            self.assertIn(line, out)
        self.assertEqual(self.site.reads.count("modules.json"), 1)  # the list of modules is read once
        code, out, err = self.post(*rows, dry=False)  # and they are posted, not only written
        self.assertEqual((code, len(self.gh.calls)), (0, 1), err)
        # Tau Ceti's own declarations do not need the list at all.
        self.site.reads.clear()
        self.assertEqual(self.post(approve("Fixture.a", V(self.a)))[0], 0)
        self.assertNotIn("modules.json", self.site.reads)

    def test_post_refuses_a_declaration_outside_the_library_that_the_site_does_not_ask_about(self):
        text = review(says="x")
        self.outside("Nat.a", "Init.Data.Nat.Basic")  # a package the site does not review
        self.outside("Nat.b", "MathlibExtras.Foo")  # begins like a reviewed package, and is not under it
        self.outside("Nat.c", None)  # in no module, and so not in the list: the last module there is one it asks about
        self.outside("Nat.d", "Mathlib.Order.Basic")
        for name, module in (("Nat.a", "Init.Data.Nat.Basic"), ("Nat.b", "MathlibExtras.Foo"), ("Nat.c", None)):
            with self.subTest(module=module):
                err = self.refused(write(name, text))
                self.assertIn(name, err)
                self.assertIn("asks its question only of", err)
                self.assertIn("Mathlib", err)  # what it does ask about
                if module:
                    self.assertIn(module, err)  # and where this one is
        # A declaration the site does not have at all is still told so.
        self.assertIn("no page", self.refused(write("Nat.nope", text)))

    def test_a_module_index_beyond_the_list_is_no_module(self):
        self.outside("Nat.e", "Mathlib.Order.Basic")
        meta = self.site.get("meta.json")
        with mock.patch.object(review_site, "get", self.site.get):
            self.assertEqual(review_site.why_not_asked(meta, "Nat.e", lambda: self.site.get("modules.json")), "")
            short = review_site.why_not_asked(meta, "Nat.e", lambda: [["Fixture", "pkg", "", ""]])  # a list too short
        self.assertIn("asks its question only of", short)

    def test_post_asks_the_site_which_packages_it_reviews(self):
        self.outside("Int.x", "Init.Data.Int.Basic")
        self.outside("Nat.y", "Mathlib.Order.Basic")
        text = review(says="x")
        both = {"Int.x", "Nat.y"}
        for outside, taken in ((["Init.Data"], {"Int.x"}), (["Mathlib"], {"Nat.y"}), (["Mathlib", "Init.Data"], both),
                               ([], set()), (None, set())):  # None: a site whose meta.json does not say
            self.site.outside = outside
            for name in ("Int.x", "Nat.y", "Fixture.b"):
                with self.subTest(outside=outside, name=name):
                    code = self.post(write(name, text))[0]
                    self.assertEqual(code, 0 if name in taken or name == "Fixture.b" else 1)

    def test_post_needs_the_site_at_the_commit(self):
        self.assertIn("deadbeef", self.refused(approve("Fixture.a", V(self.a)), commit="deadbeef"))
        code, out, err = self.cli("post", self.jsonl(approve("Fixture.a", V(self.a))), "--agent", AGENT, "--commit", "")
        self.assertEqual(code, 2)

    def test_post_needs_a_site_that_shows_standard_reviews(self):
        self.site.standard = False
        code, out, err = self.post(write("Fixture.b", review()), dry=False)
        self.assertEqual((code, out, self.gh.calls), (2, "", []))
        self.assertIn("the site does not show standard reviews yet", err)

    def test_post_refuses_what_the_intake_would_not_read(self):
        stray = {**write("Fixture.b", review()), "dropped": []}
        self.assertIn("dropped", self.refused(stray))  # a field the action does not have
        self.assertIn("text", self.refused(approve("Fixture.a", V(self.a)) | {"text": "x"}))
        # A comment changes a declaration's review once.
        self.assertIn("Fixture.b", self.refused(write("Fixture.b", review()), write("Fixture.b", review(says="again"))))
        for dash in ("—", "--"):
            item = [{"item": f"`Fixture.c_one` {dash} its value", "why": "renamed"}]
            self.assertIn("item", self.refused(edit("Fixture.c", V(self.c), review(says="c2"), "n", item)))
        self.assertIn("names a declaration", self.refused({"approve": 5, "version": "a" * 16, "cells": CELLS}))
        empty = [{"item": "`Fixture.c_one`", "why": " "}]
        self.assertIn("why", self.refused(edit("Fixture.c", V(self.c), review(says="c2"), "n", empty)))
        # An approval and a change of one declaration may share a file.
        code = self.post(approve("Fixture.a", V(self.a)), edit("Fixture.a", V(self.a), review(says="a2"), "n"))[0]
        self.assertEqual(code, 0)

    def test_post_refuses_a_text_the_intake_would_cut_short(self):
        for why, (text, whole) in BLOCKS.items():
            with self.subTest(why=why):
                code, out, err = self.post(write("Fixture.b", text))
                self.assertEqual(code, 0 if whole else 1, err)
                if not whole:
                    self.assertIn("cut short", err)

    def test_post_usage_errors(self):
        good = self.jsonl(approve("Fixture.a", V(self.a)))
        bad_json = self.dir / "bad.jsonl"
        bad_json.write_text('{"approve": "Fixture.a"\n', encoding="utf-8")
        not_object = self.dir / "list.jsonl"
        not_object.write_text('["approve"]\n', encoding="utf-8")
        empty = self.dir / "empty.jsonl"
        empty.write_text("\n\n", encoding="utf-8")
        cases = {"not JSON": [str(bad_json), "--agent", AGENT],
                 "no kind": [self.jsonl({"version": "a" * 16}, name="no_kind.jsonl"), "--agent", AGENT],
                 "two kinds": [self.jsonl({"approve": "Fixture.a", "write": "Fixture.b"}, name="two.jsonl"),
                               "--agent", AGENT],
                 "not an object": [str(not_object), "--agent", AGENT], "no actions": [str(empty), "--agent", AGENT],
                 "no file": [str(self.dir / "no"), "--agent", AGENT],
                 "no drafts file": [good, "--agent", AGENT, "--drafts", str(self.dir / "no")],
                 "a family, not a model": [good, "--agent", "Voyager, Opus"], "no model": [good, "--agent", "Voyager"]}
        for why, argv in cases.items():
            with self.subTest(why=why):
                code, out, err = self.cli("post", *argv, "--commit", COMMIT, "--dry-run")
                self.assertEqual((code, out, self.gh.calls), (2, "", []), err)
                self.assertTrue(err.startswith("error:"), err)
        for argv in (["post", good, "--commit", COMMIT], ["post", good, "--agent", AGENT]):  # --agent, --commit
            with self.subTest(argv=argv[2]):
                self.assertEqual(self.cli(*argv)[0], 2)

    def test_post_splits_between_actions_never_inside_a_block(self):
        # Review Focus 5: a batch longer than a GitHub comment goes up in several comments, each action whole.
        texts = {f"Fixture.d{i:02d}": long_review(i) for i in range(30)}
        self.assertTrue(all(2_900 < len(t) < 3_200 for t in texts.values()))
        for name in texts:
            self.site.add(name)
        code, out, err = self.post(*(write(name, text) for name, text in texts.items()), dry=False)
        self.assertEqual(code, 0, err)
        bodies = [body for _, body in self.gh.calls]
        self.assertGreaterEqual(len(bodies), 2)
        self.assertEqual(out.count("issuecomment"), len(bodies))
        self.assertIn(f"30 actions in {len(bodies)} comments", err)
        posted = []
        for body in bodies:
            self.assertLessEqual(len(body), review_site.COMMENT_CAP)
            self.assertTrue(body.startswith(HEAD))  # each comment has the agent line and the note
            posted += parse_writes(body)
        # Every action went up once, in order, with its block whole. (Hashes, so that a failure shows a short diff.)
        self.assertEqual([name for name, _ in posted], list(texts))
        self.assertEqual([V(block) for _, block in posted], [V(text) for text in texts.values()])
        # An action that no comment can hold is refused, and nothing is posted.
        self.gh.calls.clear()
        self.refused(write("Fixture.d00", review(says="z" * review_site.COMMENT_CAP)))

    def test_post_fills_a_comment_before_it_starts_the_next(self):
        cap, fixed = review_site.COMMENT_CAP, len(chunk("Fixture.big", review(says="")))
        small = [write(f"Fixture.s{i}", review(says=f"s{i}")) for i in range(2)]
        for row in small:
            self.site.add(row["write"])
        self.site.add("Fixture.big")
        # With 100 characters to spare in a comment of its own, where a small action needs more.
        big = write("Fixture.big", review(says="y" * (cap - len(HEAD) - 100 - fixed)))
        self.assertEqual(len(HEAD) + len(chunk("Fixture.big", big["text"])), cap - 100)
        code, out, err = self.post(small[0], big, small[1], dry=False)
        self.assertEqual(code, 0, err)
        names = [[n for n, _ in parse_writes(body)] for _, body in self.gh.calls]
        self.assertEqual(names, [["Fixture.s0"], ["Fixture.big"], ["Fixture.s1"]])
        self.assertTrue(all(len(body) <= cap for _, body in self.gh.calls))

    def test_post_fills_a_comment_to_its_last_character(self):
        cap, fixed = review_site.COMMENT_CAP, len(chunk("Fixture.s0", review(says="")))
        self.site.add("Fixture.s0").add("Fixture.s1")
        room = cap - len(HEAD) - 2 * fixed  # what the two texts may say between them
        for more, comments in ((0, 1), (1, 2)):
            self.gh.calls.clear()
            code, out, err = self.post(write("Fixture.s0", review(says="x" * (room // 2))),
                                       write("Fixture.s1", review(says="y" * (room - room // 2 + more))), dry=False)
            self.assertEqual((code, len(self.gh.calls)), (0, comments), err)
            if not more:
                self.assertEqual(len(self.gh.calls[0][1]), cap)

    def test_post_refuses_an_action_longer_than_a_comment(self):
        cap, fixed = review_site.COMMENT_CAP, len(chunk("Fixture.b", review(says="")))
        err = self.refused(write("Fixture.a", review(says="fine")), write("Fixture.b", review(says="z" * cap)))
        self.assertIn("Fixture.b", err)
        self.assertIn(str(cap), err.replace(",", ""))
        # A comment holds the agent line and the note as well: the action that fills it to the last character is
        # the longest one, and one character more is too long.
        room = cap - len(HEAD) - fixed
        code, out, err = self.post(write("Fixture.b", review(says="z" * room)), dry=False)
        self.assertEqual(code, 0, err)
        (_, body), = self.gh.calls
        self.assertEqual(len(body), cap)
        self.gh.calls.clear()
        self.refused(write("Fixture.b", review(says="z" * (room + 1))))

    def test_post_says_what_was_not_posted_when_gh_fails(self):
        texts = {f"Fixture.d{i:02d}": long_review(i) for i in range(30)}
        for name in texts:
            self.site.add(name)
        calls = []

        def flaky(*args, body=None):
            calls.append(body)
            if len(calls) == 2:
                review_site.die("error: gh issue comment: HTTP 502", 2)
            return "https://example.org/c"

        self.gh = flaky
        code, out, err = self.post(*(write(name, text) for name, text in texts.items()), dry=False)
        self.assertEqual((code, len(calls), out), (2, 2, "https://example.org/c\n"))
        self.assertIn("HTTP 502", err)
        self.assertIn("1 of 2 comments", err)  # the first is up
        self.assertIn("Fixture.d29", err)  # and these were not posted
        self.assertNotIn("Fixture.d00", err)


class YesTests(Case):
    def test_yes_is_gone(self):
        code, out, err = self.cli("yes", str(self.dir / "names.tsv"), "--agent", AGENT)
        self.assertEqual((code, out), (2, ""))
        self.assertIn("invalid choice", err)
        self.assertIn("'yes'", err)


class OtherCommandsTests(Case):
    """The commands that were here before still work."""

    def setUp(self):
        super().setUp()
        self.site.add("Fixture.a", entry(review()), [
            view(agent(), "2026-10-28T09:00:00Z", text="Matches the docs."),
            view(agent(), "2026-10-29T09:00:00Z", std="approved"),
            view(agent(), "2026-10-29T10:00:00Z", std="wrote"),
            view(agent("Codex", "GPT-6 Astra"), "2026-10-27T09:00:00Z", verdict="problem", text="Off by one.")])
        self.site.add("Int", None, [view(agent(), "2026-10-28T09:00:00Z", text="Mathlib's.")], project=False)

    def test_site(self):
        self.assertEqual(self.cli("site"), (0, COMMIT + "\n", ""))

    def test_check(self):
        code, out, err = self.cli("check", "Fixture.a", "Fixture.nope", "Int")
        self.assertEqual(code, 1)
        self.assertEqual(out.splitlines(), [f"site at {COMMIT}", "ON-SITE Fixture.a", "MISSING Fixture.nope",
                                            "MISSING Int"])
        self.assertEqual(self.cli("check", "Fixture.a")[0], 0)

    def test_check_and_no_still_take_only_tau_cetis_own_declarations(self):
        self.site.add("Nat.foo", entry(review()), module="Mathlib.Data.Nat.Basic", project=False)  # one `post` takes
        code, out, err = self.cli("check", "Nat.foo")
        self.assertEqual((code, out.splitlines()[1:]), (1, ["MISSING Nat.foo"]))
        why = self.dir / "why.md"
        why.write_text("It is off by one.\n", encoding="utf-8")
        code, out, err = self.cli("no", str(why), "--agent", AGENT, "--decl", "Nat.foo", "--commit", COMMIT[:12],
                                  "--category", "object", "--involvement", "outsider")
        self.assertEqual((code, out), (1, ""))
        self.assertIn("the site has no page for Nat.foo", err)

    def test_reviews_says_what_a_record_of_the_standard_review_did(self):
        code, out, err = self.cli("reviews", "Fixture.a", "Fixture.nope", "Int")
        self.assertEqual(code, 0, err)
        self.assertIn("Fixture.a: 4 answers", out)
        self.assertIn("2026-10-28: Matches the docs.", out)
        self.assertIn("2026-10-29: approved the standard review", out)
        self.assertIn("2026-10-29: wrote the standard review", out)
        self.assertIn("Off by one.", out)
        self.assertNotIn("(no reasons)", out)
        self.assertIn("Fixture.nope: the site has no such declaration", out)
        self.assertIn("2026-10-28: Mathlib's.", out)

    def test_no(self):
        why = self.dir / "why.md"
        why.write_text("It is off by one.\n", encoding="utf-8")
        ran = []

        def run(cmd, **kw):
            ran.append(cmd)
            return subprocess.CompletedProcess(cmd, 0, stdout=f"https://github.com/{review_site.REPO}/issues/12\n",
                                               stderr="")

        with mock.patch.object(review_site.subprocess, "run", run):
            code, out, err = self.cli("no", str(why), "--agent", AGENT, "--decl", "Fixture.a", "--commit", COMMIT[:12],
                                      "--category", "object", "--involvement", "outsider")
        self.assertEqual(code, 0, err)
        self.assertEqual(out, f"issue 12 https://github.com/{review_site.REPO}/issues/12\n")
        self.assertIn("problem", ran[0])
        self.assertIn(COMMIT, ran[0])


def site_checkouts():
    """Where the review site's repository may be: $TAUCETI_REVIEW_SITE_DIR, the usual place, or beside this one."""
    chosen = [os.environ.get("TAUCETI_REVIEW_SITE_DIR"), "~/GitHub/tauceti-reviewed-by-test"]
    return [Path(p).expanduser() for p in chosen if p] + [HERE.parent.parent / "tauceti-reviewed-by-test"]


class IntakeReadsPostTests(Case):
    """What `post --dry-run` writes, read by the review site's own parser (scripts/standard_intake.py) and the checks
    its intake makes of a line (scripts/standard.py): a change there that `post` does not follow fails here."""

    @classmethod
    def setUpClass(cls):
        found = next((p for p in site_checkouts() if (p / "scripts" / "standard_intake.py").is_file()), None)
        if found is None:
            raise unittest.SkipTest("the review site's repository is not here: set TAUCETI_REVIEW_SITE_DIR to it")
        scripts = str(found / "scripts")
        sys.path.insert(0, scripts)
        cls.addClassCleanup(sys.path.remove, scripts)
        try:
            import evidence_core  # noqa: F401
        except ImportError:  # the packages the site pins are in its own .venv: take them from there, last in the path
            sys.path += [str(p) for p in sorted(found.glob(".venv/lib/python*/site-packages"))]
        try:
            import standard
            import standard_intake
            from evidence_core.rubric import STANDARD
            from evidence_store import intake
        except ImportError as e:
            raise unittest.SkipTest(f"the site's scripts need evidence-core and evidence-store ({e}): "
                                    "run with the python of the site's .venv")
        cls.standard, cls.si, cls.rubric, cls.intake = standard, standard_intake, STANDARD, intake
        cls.common = __import__("common")

    def comments(self, out):
        """The comments a dry run printed, each from its agent line on."""
        return [c for c in re.split(r"(?m)^(?=<!-- agent:)", out) if c.strip()]

    def test_the_parser_reads_every_line(self):
        std = self.standard
        a = review(says="a")
        c = review(says="c", refs=("- Fixture documentation, §1.", "- `Fixture.c_one` — its value at 1",
                                   "- Check *test_one*, `Fixture/Examples.lean:1` — passes"))
        # An awkward text: code fences of both kinds inside it, a line that looks like a command before the first
        # `~~~` line of the text, and CRLF line ends with trailing spaces, as an editor leaves them.
        b = review(says="b, with `code`:\n```lean\ndef x := 1\n```\n"
                        "Test: a command line before any tilde fence is text\n~~~lean\ndef y := 2\n~~~\nand more")
        b_raw = "\n" + b.replace("\n", "  \r\n") + "\n"
        c2 = review(says="c, more", refs=("- Fixture documentation, §1.", "- `Fixture.c_uno` — its value at 1"))
        dropped = [{"item": "`Fixture.c_one`", "why": "renamed `Fixture.c_uno` — in Tau Ceti"},
                   {"item": "Check *test_one*", "why": "no longer there"}]
        note = "renames the test — and drops a Check"
        o = review(says="`Nat.o` is a successor, in Mathlib")
        self.site.add("Fixture.a", entry(a)).add("Fixture.b").add("Fixture.c", entry(c))
        self.outside("Nat.o", "Mathlib.Data.Nat.Basic", o)  # one of Mathlib's, which the site asks about
        code, out, err = self.post(approve("Fixture.a", V(a)[:8].upper()), write("Fixture.b", b_raw),
                                   edit("Fixture.c", V(c), c2, note, dropped), approve("Nat.o", V(o)))
        self.assertEqual(code, 0, err)
        comments = self.comments(out)
        self.assertEqual(len(comments), 1)
        # The agent line is the intake's: the same tool, model and session.
        self.assertEqual(self.intake.parse_agent_mark(comments[0]),
                         {"tool": "Voyager", "model": "claude-fable-5-1", "session": "7"})
        approval, written, edited, outside = self.si.commands(comments[0])
        self.assertEqual([(x.keyword, x.fields[0]) for x in (approval, written, edited, outside)],
                         [("Approve", "Fixture.a"), ("Write", "Fixture.b"), ("Edit", "Fixture.c"),
                          ("Approve", "Nat.o")])
        # Each line has the fields of the form the intake gives an agent, and cells that are the rubric's.
        forms = [self.si.given(x, self.si.FORMS[x.keyword, True]) for x in (approval, written, edited, outside)]
        self.assertNotIn(None, forms)
        for f in forms:
            self.assertEqual(std.cells(f["cells"], self.rubric.names), (CELLS, ""))
        self.assertEqual(self.si.named(forms[0]["version"], {V(a)}), {V(a)})  # 8 digits, in capitals, name a version
        self.assertEqual(self.si.named(forms[2]["parent"], {V(c)}), {V(c)})
        self.assertEqual((forms[3]["decl"], self.si.named(forms[3]["version"], {V(o)})), ("Nat.o", {V(o)}))
        # A text reaches the intake whole, and is the version the agent hashed; it passes the intake's check.
        self.assertEqual(written.block, std.normalize(b_raw))
        self.assertEqual(std.version_of(written.block), V(b_raw))
        self.assertEqual(std.check(written.block), [])
        self.assertEqual(edited.block, std.normalize(c2))
        self.assertEqual(edited.dropped, [(d["item"], d["why"]) for d in dropped])
        self.assertEqual(forms[2]["note"], note)
        self.assertEqual(std.check(edited.block, parent=c, dropped=edited.dropped, note=forms[2]["note"]), [])
        # A Dropped line and a block go with the line before them.
        self.assertEqual((approval.block, approval.dropped, written.dropped), (None, [], []))

    def test_a_long_batch_is_read_whole_in_every_comment(self):
        texts = {f"Fixture.d{i:02d}": long_review(i) for i in range(30)}
        for name in texts:
            self.site.add(name)
        code, out, err = self.post(*(write(name, text) for name, text in texts.items()))
        self.assertEqual(code, 0, err)
        comments = self.comments(out)
        self.assertGreaterEqual(len(comments), 2)
        read = []
        for comment in comments:
            self.assertLessEqual(len(comment.rstrip("\n")) + 1, review_site.COMMENT_CAP)
            self.assertIsNotNone(self.intake.parse_agent_mark(comment))
            for cmd in self.si.commands(comment):
                self.assertEqual(cmd.keyword, "Write")
                self.assertEqual(self.standard.check(cmd.block), [])
                read.append((cmd.fields[0], cmd.block))
        self.assertEqual([name for name, _ in read], list(texts))
        self.assertEqual([V(block) for _, block in read], [V(text) for text in texts.values()])

    def test_the_copies_agree_with_the_sites(self):
        std = self.standard
        # normalize and version_of: the vector, and every kind of line end and white space.
        samples = [VECTOR, "", "\n", " \n", "a", "a  \r\n", "a\r\rb\r\n", "a\u00a0\nb\u3000", "a\u2028b\u2029\n",
                   "a\x85\nb\x0b\n", "a\x1c\nb\x1f\n", "\ufeffa\n", "\t\n\ta\t\n\n\n", "§ℂ𝔾  \r\nb\r\n"]
        for s in samples:
            with self.subTest(text=s):
                self.assertEqual(review_site.normalize(s), std.normalize(s))
                self.assertEqual(review_site.version_of(s), std.version_of(s))
        # The shard of a name is the site's, and so are the rubric's axes and the headings.
        for name in ("TauCeti.Foo.bar", "Fixture.triple", "Int", "TauCeti.α₁.𝔾", "Nat.add_comm"):
            for shards in (4, 64, 256):
                self.assertEqual(review_site.fnv(name, shards), self.common.fnv_shard(name, shards))
        self.assertEqual(review_site.RUBRIC, list(self.rubric.names))
        self.assertEqual(tuple(review_site.HEADINGS), std.HEADINGS)

    def test_the_site_asks_about_the_declarations_post_takes(self):
        try:
            import site_data
        except ImportError as e:
            self.skipTest(f"the site's build needs more of evidence-core ({e})")
        modules = (None, "", "Mathlib", "Mathlib.Data.Nat.Basic", "MathlibExtras.Foo", "Init.Data",
                   "Init.Data.Int.Basic", "Init.Prelude", "Fixture.Basic")
        for outside in (None, [], ["Mathlib"], ["Init.Data"], ["Mathlib", "Init.Data"]):
            settings = {} if outside is None else {"review_outside": outside}
            asks = types.SimpleNamespace(inp=types.SimpleNamespace(settings=settings))
            for project in (True, False):
                for module in modules:
                    with self.subTest(outside=outside, project=project, module=module):
                        site = Site(outside=outside).add("W", module="Mathlib.Order.Basic", project=False)
                        site.add("X", module=module, project=project)
                        with mock.patch.object(review_site, "get", site.get):
                            ours = review_site.why_not_asked(site.get("meta.json"), "X",
                                                             lambda: site.get("modules.json"))
                        decl = types.SimpleNamespace(is_project=project, module=module)
                        self.assertEqual(ours == "", site_data.Site.answerable(asks, decl), ours)

    def test_the_local_checks_agree_with_the_sites(self):
        std = self.standard
        heads = list(std.HEADINGS)
        texts = [review(), VECTOR, "", "x", "\n".join([heads[0], "a", heads[1], "b", heads[2], "c"]),
                 "\n".join([heads[0], "a", heads[1], "b"]), "\n".join([heads[1], "b", heads[0], "a", heads[2], "c"]),
                 "A title\n" + review(), review() + heads[0] + "\ntwice", review(subtle=""), review(says=" "),
                 review().replace("## What it says", "## What it says "), review().replace("## ", "# "),
                 review().replace("\n", "\r\n"), "\n".join([heads[0], "  ", heads[1], "b", heads[2], "c"])]
        for text in texts:
            with self.subTest(text=text[:50]):
                self.assertEqual(bool(review_site.text_problems(text)), bool(std.parts(text)[1]))
        # Cells: what is a cell list to the intake is the cells `post` writes, and the list it writes reads back.
        for spec, want in {CELLS_LINE: CELLS, "object": None, "": None, f"{CELLS_LINE}, naming": None,
                           CELLS_LINE.replace("choice n/a", "choice=checked"): {**CELLS, "choice": "checked"}}.items():
            self.assertEqual(std.cells(spec, self.rubric.names)[0], want)
        # A block read back whole: the intake's own reading of a block says so, for each of these texts.
        for why, (text, whole) in BLOCKS.items():
            with self.subTest(why=why):
                comment = f"Write: X — cells\n~~~review\n{std.normalize(text)}\n~~~\nTest: X — Y — z"
                self.assertEqual(self.si.commands(comment)[0].block == std.normalize(text), whole)
                self.assertEqual(review_site.block_whole(std.normalize(text)), whole)
        self.assertEqual(review_site.cell_problems(CELLS), [])
        self.assertEqual(review_site.cells_line(CELLS), CELLS_LINE)
        every = {**CELLS, "naming": "na", "object": "na"}
        self.assertEqual(std.cells(review_site.cells_line(every), self.rubric.names)[0], every)


if __name__ == "__main__":
    unittest.main()
