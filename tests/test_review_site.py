"""Tests of scripts/review_site.py: the commands of the standard review (`standard`, `hash`, `guide`, `post`) and the
commands beside them. The review site is faked by patching `review_site.get` (its data) and `review_site.fetch` (a text
file of GitHub's), and GitHub by patching `review_site.gh`: nothing here touches the network or GitHub.

`AstraQuestionTests` and `AstraAnswerTests` (`astra-question`, `astra-answer`) build a real git repository for the Tau
Ceti checkout, in a temporary directory, and let `git -C` of that checkout run: nothing else may.

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

#: The real `subprocess.run`, taken before any test patches it: the tests of the questions to Astra run git with it.
REAL_RUN = subprocess.run
#: The environment those git calls get: none of git's own variables (`GIT_DIR`, ... when a hook runs the tests), which
#: would point `git -C <the fixture>` at another repository.
GIT_ENV = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}

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


def norm(text):
    return review_site.normalize(text)


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
    return f"Write: {decl} — {CELLS_LINE}\n~~~review\n{norm(text)}\n~~~\n"


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
    views, and the standard reviews the site shows. The library has one module, `Fixture`, in the file ``path``; a
    declaration outside it may be in a module of its own (modules.json lists them). ``outside`` is the packages whose
    declarations the site asks its question of (`meta.review.outside`), or None for a site that does not say. ``reads``
    lists what was asked of it.

    A declaration may say more of itself, as keywords of `add`: its kind code ``k`` (default `t`), its signature
    ``sig`` (or ``stmt``), the ``line`` range of its source in the file, and the names it ``rests`` on."""
    NODES, NAMES, STANDARD = 4, 4, 256

    def __init__(self, commit=COMMIT, standard=True, bulk=1, outside=("Mathlib",), path="Fixture.lean"):
        self.commit, self.standard, self.bulk, self.outside, self.path = commit, standard, bulk, outside, path
        self.decls, self.reviews, self.modules, self.reads, self.info = [], {}, ["Fixture"], [], {}

    def add(self, name, review=None, records=(), project=True, module=None, **info):
        if module and module not in self.modules:
            self.modules.append(module)
        self.decls.append((name, project, list(records), module))
        if review:
            self.reviews[name] = review
        if info:
            self.info[name] = info
        return self

    def id_of(self, name):
        return next(i for i, decl in enumerate(self.decls) if decl[0] == name)

    def node(self, name, project, module):
        """A row of nodes/<k>.json: name, kind, flags, module index, title, two states, what it rests on, and the
        columns between that and how many things it rests on."""
        rests = [self.id_of(x) for x in self.info.get(name, {}).get("rests", ())]
        return [name, self.info.get(name, {}).get("k", "t"), 1 if project else 0,
                0 if project else self.modules.index(module) if module else -1, "", 0, 0, rests, [], len(rests)]

    def entry(self, i, name, **more):
        """An entry of a module's file: the statement and the lines it was declared on, when the declaration says."""
        said = self.info.get(name, {})
        return {"id": i, "name": name, "k": said.get("k", "t"),
                **{x: v for x, v in said.items() if x in ("sig", "stmt", "line")}, **more}

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
            return [self.node(name, project, module)
                    for name, project, _, module in self.decls[k * self.NODES:(k + 1) * self.NODES]]
        if kind == "m":
            return {"name": self.modules[0], "path": self.path,
                    "decls": [self.entry(i, name, records=records)
                              for i, (name, project, records, _) in enumerate(self.decls) if project]}
        if kind == "u":
            return {"name": self.modules[k],
                    "decls": [self.entry(i, name) for i, (name, project, _, module) in enumerate(self.decls)
                              if not project and module == self.modules[k]]}
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


#: A Tau Ceti file for the questions to Astra; the `line` range of each declaration of the fixture site is in it.
SOURCE = (
    "import Mathlib\n"  # 1
    "\n"
    "namespace Fixture\n"
    "\n"
    "/-- `triple n` is three times `n`. -/\n"  # 5
    "def triple (n : ℕ) : ℕ := 3 * n\n"
    "\n"
    "/-- Tripling twice is multiplying by nine. -/\n"  # 8
    "theorem triple_triple (n : ℕ) : triple (triple n) = 9 * n := by\n"
    "  unfold triple\n"
    "  omega\n"  # 11
    "\n"
    "theorem triple_two : triple 2 = 6 := by\n"  # 13
    "  decide\n"
    "\n"
    "end Fixture\n")
#: The cells of an answer, as the instructions to Astra show them.
ANSWER_CELLS = ("object=checked, convention=checked, edge-cases=checked, junk=checked, vacuous=checked, "
                "choice=n/a, generality=checked, naming=checked")


def error_cells(axis, why="the statement is wrong"):
    """The cells of an answer in which the check ``axis`` found an error."""
    return ANSWER_CELLS.replace(f"{axis}=checked", f"{axis}=ERROR: {why}")


def item(n, name, verdict, *lines, cells=ANSWER_CELLS, block=None):
    """Astra's answer to item ``n`` of a question: the cells and the verdict (left out when None), the lines the verdict
    takes, and the block of the whole text."""
    out = [f"### {n}. {name}"] + ([f"CELLS: {cells}"] if cells is not None else []) \
        + ([f"VERDICT: {verdict}"] if verdict is not None else []) + list(lines)
    if block is not None:
        out += ["~~~review", block.strip("\n"), "~~~"]
    return "\n".join(out) + "\n\n"


class AstraCase(Case):
    """Questions to Astra and their answers, against a Tau Ceti checkout that is a real git repository (one `.lean`
    file, one commit) and a site that describes it. Of everything that runs, only `git -C <the checkout>` may."""
    PATH = "Fixture/Basic.lean"
    GUIDE = "## The standard review\n\nEach declaration has one standard review.\n"
    DOC = (f"# Reviewing\n\nIntro.\n\n{review_site.GUIDE_BEGIN}\n{GUIDE}{review_site.GUIDE_END}\n\n"
           "## What you need\n\nElsewhere.\n")

    def setUp(self):
        super().setUp()
        if shutil.which("git") is None:
            self.skipTest("git is not installed")
        self.repo, self.git_calls = self.dir / "TauCeti", []
        self.commit = self.commit_files({self.PATH: SOURCE})
        patcher = mock.patch.object(review_site.subprocess, "run", self.run_git)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.site = Site(commit=self.commit, path=self.PATH)
        self.t1, self.t2, self.t3 = review(says="triple"), review(says="triple twice"), review(says="two")
        self.site.add("Fixture.triple", entry(self.t1), k="d", line=[5, 6], sig="Fixture.triple (n : ℕ) : ℕ")
        self.site.add("Fixture.triple_triple", entry(self.t2), line=[8, 11], rests=["Fixture.triple"],
                      sig="Fixture.triple_triple (n : ℕ) : Fixture.triple (Fixture.triple n) = 9 * n")
        self.site.add("Fixture.triple_two", entry(self.t3), line=[13, 14], rests=["Fixture.triple", "Nat.mul"],
                      sig="Fixture.triple_two : Fixture.triple 2 = 6")
        self.site.add("Nat.mul", None, project=False, module="Init.Prelude", k="d", sig="Nat.mul : ℕ → ℕ → ℕ")

    def git(self, *args):
        """git in the checkout, to build it: the real `run`, which the guard of `run_git` keeps from everything else."""
        done = REAL_RUN(["git", "-C", str(self.repo), "-c", "user.name=T", "-c", "user.email=t@example.org", "-c",
                         "commit.gpgsign=false", "-c", "core.autocrlf=false", "-c", f"core.hooksPath={os.devnull}",
                         *args], capture_output=True, text=True, env=GIT_ENV)
        self.assertEqual(done.returncode, 0, done.stderr)
        return done.stdout.strip()

    def commit_files(self, files):
        """Commits ``files`` (path to text or bytes) to the checkout, which is made if need be: the new commit."""
        self.repo.mkdir(exist_ok=True)
        if not (self.repo / ".git").exists():
            self.git("init", "-q")
        for path, content in files.items():
            (self.repo / path).parent.mkdir(parents=True, exist_ok=True)
            (self.repo / path).write_bytes(content.encode("utf-8") if isinstance(content, str) else content)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "fixture")
        return self.git("rev-parse", "HEAD")

    def run_git(self, cmd, **kw):
        """`subprocess.run` for the code under test: git in the checkout runs, and is recorded; anything else fails."""
        if list(cmd[:3]) != ["git", "-C", str(self.repo)]:
            raise AssertionError(f"unexpected call of run: {cmd}")
        self.git_calls.append(list(cmd[3:]))
        return REAL_RUN(cmd, **{"env": GIT_ENV, **kw})

    def question(self, *names, drafts=None, tauceti=None, out="question.txt"):
        """(exit code, stdout, stderr) of `astra-question NAMES`, written to the file ``out`` of the temporary
        directory."""
        return self.cli("astra-question", *names, "--tauceti", tauceti or str(self.repo), "--out", str(self.dir / out),
                        *(["--drafts", drafts] if drafts else []), fetch=lambda url: self.DOC)

    def ask(self, *names, **kw):
        """The path of the question about ``names``, which must be written."""
        code, out, err = self.question(*names, **kw)
        self.assertEqual((code, out), (0, ""), err)
        return str(self.dir / kw.get("out", "question.txt"))

    @staticmethod
    def items(text):
        """The items of a question, each from its heading on: the declarations, not the examples of the instructions."""
        return re.split(r"(?m)^(?=### \d+\. )", text.split("\n## The declarations\n", 1)[1])[1:]


class AstraQuestionTests(AstraCase):
    def test_question_holds_source_rests_on_and_review(self):
        text = Path(self.ask("Fixture.triple_two", "Fixture.triple_triple")).read_text(encoding="utf-8")
        # Three things, in this order: the instructions, the guide's section, the numbered items.
        look, guide, first = (text.index(x) for x in
                              ("Look for errors in the Lean first", self.GUIDE.strip(), "### 1. Fixture.triple_two"))
        self.assertLess(look, guide)
        self.assertLess(guide, first)
        for want in ("ERROR:", "VERDICT: NO", "CATEGORY:", "WHY:", "APPROVE", "EDIT", "WRITE", "~~~review", "NOTE:",
                     "DROPPED:", *AXES):
            self.assertIn(want, text[:guide])
        self.assertIn("Write nothing after your last item", text[:guide])
        self.assertNotIn(review_site.GUIDE_BEGIN, text)  # the section, not its markers
        one, two = self.items(text)
        self.assertTrue(one.startswith("### 1. Fixture.triple_two\n"))
        self.assertIn("Kind: theorem", one)
        self.assertIn(f"Source: {self.PATH}, lines 13 to 14, at Tau Ceti {self.commit[:12]}", one)
        self.assertIn("```lean\ntheorem triple_two : triple 2 = 6 := by\n  decide\n```", one)
        self.assertNotIn("end Fixture", one)  # the lines of the declaration, not the rest of the file
        self.assertNotIn("3 * n", one)  # what it rests on is shown by its statement, not its source
        rests = one.split("Rests on:")[1].split("Current standard review")[0]
        self.assertEqual([x for x in rests.splitlines() if x.strip()],
                         ["- Fixture.triple: Fixture.triple (n : ℕ) : ℕ", "- Nat.mul: Nat.mul : ℕ → ℕ → ℕ"])
        self.assertIn(f"Version: {V(self.t3)}\n~~~review\n{self.t3.strip(chr(10))}\n~~~", one)
        self.assertTrue(two.startswith("### 2. Fixture.triple_triple\n"))
        self.assertIn("/-- Tripling twice is multiplying by nine. -/\ntheorem triple_triple", two)
        self.assertIn("  unfold triple\n  omega\n```", two)
        self.assertEqual([x for x in two.split("Rests on:")[1].splitlines() if x.startswith("- ")][:1],
                         ["- Fixture.triple: Fixture.triple (n : ℕ) : ℕ"])
        self.assertIn(f"Version: {V(self.t2)}", two)
        # The Lean is read from the commit the site shows, in the checkout: the file once for the two declarations.
        self.assertEqual(self.git_calls, [["cat-file", "-e", f"{self.commit}^{{commit}}"],
                                          ["show", f"{self.commit}:{self.PATH}"]])
        # And each file of the site once: the module's file is read for both, and for what they rest on.
        self.assertEqual(self.site.reads.count("m/0.json"), 1)
        self.assertEqual(len(self.site.reads), len(set(self.site.reads)))

    def test_question_uses_a_draft_over_the_site(self):
        self.site.add("Fixture.d", entry(review(says="d, on the site")), line=[13, 14], sig="Fixture.d : True")
        self.site.add("Fixture.e", None, line=[13, 14], sig="Fixture.e : True")
        self.site.add("Fixture.f", None, line=[13, 14], sig="Fixture.f : True")
        edited, written = review(says="triple twice, edited"), review(says="e, written")
        drafts = self.jsonl(edit("Fixture.triple_triple", V(self.t2), edited, "says more"), write("Fixture.e", written),
                            approve("Fixture.triple", V(self.t1)), name="drafts.jsonl")
        text = Path(self.ask("Fixture.triple", "Fixture.triple_triple", "Fixture.d", "Fixture.e", "Fixture.f",
                             drafts=drafts)).read_text(encoding="utf-8")
        triple, triple_triple, d, e, f = self.items(text)
        # A draft of the declaration is its current review, its version the hash of the draft's text, whatever the
        # site shows.
        self.assertIn(f"Version: {V(edited)}\n~~~review\n{edited.strip(chr(10))}\n~~~", triple_triple)
        self.assertNotIn(V(self.t2), triple_triple)
        self.assertNotIn("triple twice\n", triple_triple)
        self.assertIn(f"Version: {V(written)}\n~~~review\n{written.strip(chr(10))}\n~~~", e)
        # An approval is no draft of a text, and a declaration without a draft shows the site's review.
        self.assertIn(f"Version: {V(self.t1)}", triple)
        self.assertIn(f"Version: {V(review(says='d, on the site'))}", d)
        # A declaration with neither is told there is none, and is to be written.
        self.assertIn("Current standard review: (no standard review yet: write one)", f)
        self.assertNotIn("Version:", f)
        # Several drafts of one declaration: the last is the current one.
        later = review(says="e, written again")
        drafts = self.jsonl(write("Fixture.e", written), edit("Fixture.e", V(written), later, "again"), name="d2.jsonl")
        self.assertIn(f"Version: {V(later)}", self.items(Path(self.ask("Fixture.e", drafts=drafts)).read_text(
            encoding="utf-8"))[0])

    def test_question_refuses_more_than_12(self):
        names = [f"Fixture.x{i:02d}" for i in range(13)]
        for name in names:
            self.site.add(name, entry(review(says=name)), line=[13, 14], sig=f"{name} : True")
        code, out, err = self.question(*names)
        self.assertEqual((code, out), (1, ""))
        self.assertIn("refused", err)
        self.assertIn("at most 12", err)
        self.assertFalse((self.dir / "question.txt").exists())
        self.assertEqual((self.site.reads, self.git_calls), ([], []))  # refused before anything was read
        text = Path(self.ask(*names[:12])).read_text(encoding="utf-8")  # twelve are fine
        self.assertEqual([x.splitlines()[0] for x in self.items(text)],
                         [f"### {k}. {name}" for k, name in enumerate(names[:12], 1)])

    def test_question_refuses_what_it_cannot_ask_about(self):
        self.site.add("Fixture.nolines", entry(review()), sig="Fixture.nolines : True")
        names = ["Fixture.triple", "Fixture.nope", "Nat.mul", "Fixture.nolines"]
        code, out, err = self.question(*names)
        self.assertEqual((code, out), (1, ""))
        self.assertIn("refused", err)
        for name, why in (("Fixture.nope", "no page"), ("Nat.mul", "Tau Ceti's own"), ("Fixture.nolines", "source")):
            self.assertRegex(err, rf"{re.escape(name)}: .*{why}")  # all of them at once, each with its reason
        self.assertNotIn("Fixture.triple:", err)  # the name that is fine is not named
        self.assertFalse((self.dir / "question.txt").exists())
        self.assertEqual(self.git_calls, [])
        code, out, err = self.question("Fixture.triple", "Fixture.triple_two", "Fixture.triple")
        self.assertEqual((code, out), (1, ""))
        self.assertRegex(err, r"Fixture\.triple .*twice")

    def test_question_needs_the_commit_in_the_checkout(self):
        self.site.commit = "1" * 40
        code, out, err = self.question("Fixture.triple")
        self.assertEqual((code, out), (2, ""))
        self.assertIn("1" * 12, err)  # the commit the site shows
        self.assertIn("fetch", err)  # and what to do
        self.assertFalse((self.dir / "question.txt").exists())
        # A file the commit lacks, and a checkout that is no directory, are told too.
        self.site.commit, self.site.path = self.commit, "Fixture/Gone.lean"
        code, out, err = self.question("Fixture.triple")
        self.assertEqual((code, out), (2, ""))
        self.assertIn("Fixture/Gone.lean", err)
        self.site.path = self.PATH
        code, out, err = self.question("Fixture.triple", tauceti=str(self.dir / "nowhere"))
        self.assertEqual((code, out), (2, ""))
        self.assertIn("nowhere", err)
        self.assertFalse((self.dir / "question.txt").exists())

    def test_question_gives_the_source_whatever_its_line_ends(self):
        self.site.commit = self.commit_files({"Crlf.lean": b"namespace Crlf\r\ntheorem t : True := by\r\n  trivial\r\n"
                                                           b"end Crlf\r\n"})
        self.site.path = "Crlf.lean"
        self.site.add("Crlf.t", entry(review()), line=[2, 3], sig="Crlf.t : True")
        text = Path(self.ask("Crlf.t")).read_text(encoding="utf-8")
        self.assertIn("```lean\ntheorem t : True := by\n  trivial\n```", text)
        self.assertNotIn("\r", text)

    def test_question_shows_the_source_in_a_fence_that_can_hold_it(self):
        src = "/-- Use\n```lean\nexample : True := trivial\n```\nlike this. -/\ntheorem t : True := trivial\n"
        self.site.commit = self.commit_files({"Fences.lean": src})
        self.site.path = "Fences.lean"
        self.site.add("Fences.t", entry(review()), line=[1, 6], sig="Fences.t : True")
        one, = self.items(Path(self.ask("Fences.t")).read_text(encoding="utf-8"))
        self.assertIn("````lean\n" + src.rstrip("\n") + "\n````", one)  # a fence longer than the one in the source

    def test_question_shows_at_most_12_statements_it_rests_on(self):
        rests = [f"Nat.l{i:02d}" for i in range(14)]
        for name in rests:
            self.site.add(name, None, project=False, module="Mathlib.Data.Nat.Basic", k="t", sig=f"{name} : P")
        self.site.add("Fixture.big", entry(review()), line=[13, 14], rests=rests, sig="Fixture.big : True")
        one, = self.items(Path(self.ask("Fixture.big")).read_text(encoding="utf-8"))
        shown = one.split("Rests on:")[1].split("Current standard review")[0]
        listed = [x for x in shown.splitlines() if x.startswith("- ")]
        self.assertEqual(listed[:12], [f"- {name}: {name} : P" for name in rests[:12]])  # the node's order
        self.assertEqual(len(listed), 13)
        self.assertIn("2 more", listed[12])
        self.assertNotIn(rests[12], one)

    def test_question_says_what_it_rests_on_by_what_the_site_has(self):
        self.site.add("Fixture.stated", None, stmt="theorem stated : 1 = 1", line=[13, 14])  # no signature, a statement
        self.site.add("Fixture.bare", None, line=[13, 14])  # neither
        self.site.add("Fixture.top", entry(review()), line=[13, 14], rests=["Fixture.stated", "Fixture.bare"], sig="x")
        self.site.add("Fixture.lone", entry(review()), line=[13, 14], sig="Fixture.lone : True")  # rests on nothing
        top, lone = self.items(Path(self.ask("Fixture.top", "Fixture.lone")).read_text(encoding="utf-8"))
        self.assertIn("- Fixture.stated: theorem stated : 1 = 1", top)
        self.assertRegex(top, r"- Fixture\.bare: \(.*no statement.*\)")
        self.assertRegex(lone, r"Rests on: .*nothing")

    def test_question_warns_when_it_is_longer_than_one_argument_can_be(self):
        self.assertNotIn("warning", self.question("Fixture.triple")[2])
        with mock.patch.object(review_site, "QUESTION_WARN", 1000):
            code, out, err = self.question("Fixture.triple")
        self.assertEqual((code, out), (0, ""))
        self.assertIn("warning", err)  # the question is still written
        self.assertTrue((self.dir / "question.txt").exists())

    def test_question_needs_the_guide_and_a_site_with_standard_reviews(self):
        def unreadable(url):
            raise OSError("no route")

        code, out, err = self.cli("astra-question", "Fixture.triple", "--tauceti", str(self.repo), "--out",
                                  str(self.dir / "question.txt"), fetch=unreadable)
        self.assertEqual((code, out), (2, ""))
        self.assertIn("no route", err)
        code, out, err = self.question("Fixture.triple", drafts=str(self.dir / "nowhere.jsonl"))
        self.assertEqual((code, out), (2, ""))
        self.assertIn("nowhere.jsonl", err)
        self.site.standard = False
        code, out, err = self.question("Fixture.triple")
        self.assertEqual((code, out), (2, ""))
        self.assertIn("the site does not show standard reviews yet", err)
        self.assertFalse((self.dir / "question.txt").exists())


class AstraAnswerTests(AstraCase):
    def setUp(self):
        super().setUp()
        self.t4 = review(says="d")
        self.site.add("Fixture.d", entry(self.t4), line=[13, 14], sig="Fixture.d : True")
        self.site.add("Fixture.e", None, line=[13, 14], sig="Fixture.e : True")  # no review: to be written

    def answer(self, question, *parts, name="answer.md"):
        """(exit code, stdout, stderr, actions, noes) of `astra-answer` on the answer ``parts``, with the two files it
        writes as lists of rows."""
        path, actions, noes = self.dir / name, self.dir / "actions.jsonl", self.dir / "noes.jsonl"
        path.write_bytes("".join(parts).encode("utf-8"))
        self.site.reads.clear()
        git_calls = len(self.git_calls)
        code, out, err = self.cli("astra-answer", str(path), "--question", question, "--out", str(actions), "--noes",
                                  str(noes))
        rows = lambda p: [json.loads(x) for x in p.read_text(encoding="utf-8").splitlines()] if p.exists() else None
        # The answer needs nothing but its question: no site, no checkout.
        self.assertEqual((self.site.reads, self.git_calls[git_calls:]), ([], []))
        return code, out, err, rows(actions), rows(noes)

    def test_answer_to_actions_and_noes(self):
        q = self.ask("Fixture.triple", "Fixture.triple_triple", "Fixture.triple_two", "Fixture.d", "Fixture.e")
        edited, written = review(says="triple twice, said better"), review(says="e")
        why = "`triple 0 = 0`, not 6, so the statement needs `n ≠ 0`."
        code, out, err, actions, noes = self.answer(
            q, "Here are my reviews.\n\n",
            item(1, "Fixture.triple", "APPROVE"),
            item(2, "Fixture.triple_triple", "EDIT", "NOTE: adds the hypothesis the statement skips",
                 "DROPPED: `Fixture.triple_triple_one` — renamed `Fixture.triple_triple_uno` in Tau Ceti",
                 "DROPPED: Check *test_one* -- no longer in the roadmap", block=edited),
            item(3, "Fixture.triple_two", "NO", f"CATEGORY: edge-cases   WHY: {why}",
                 cells=error_cells("edge-cases", "it fails at 0")),
            item(4, "Fixture.d", "APPROVE", cells=ANSWER_CELLS.replace(", naming=checked", "")),  # a cell is missing
            item(5, "Fixture.e", "WRITE", block=written))
        self.assertEqual(code, 0, err)
        dropped = [{"item": "`Fixture.triple_triple_one`", "why": "renamed `Fixture.triple_triple_uno` in Tau Ceti"},
                   {"item": "Check *test_one*", "why": "no longer in the roadmap"}]
        # In the order of the question; versions from the question, texts as they will be posted.
        self.assertEqual(actions, [
            approve("Fixture.triple", V(self.t1)),
            edit("Fixture.triple_triple", V(self.t2), norm(edited),
                 "adds the hypothesis the statement skips", dropped),
            write("Fixture.e", norm(written))])
        self.assertEqual(noes, [{"decl": "Fixture.triple_two", "category": "edge-cases", "why": why}])
        self.assertEqual(len(out.splitlines()), 1, out)
        self.assertRegex(out, r"^not filed: Fixture\.d: .*missing naming")
        self.assertIn("3 actions", err)

    def test_answer_writes_the_first_review(self):
        q = self.ask("Fixture.e", "Fixture.triple")
        text = Path(q).read_text(encoding="utf-8")
        self.assertIn("(no standard review yet: write one)", self.items(text)[0])
        written = review(says="e says this")
        code, out, err, actions, noes = self.answer(q, item(1, "Fixture.e", "WRITE", block=written))
        self.assertEqual((code, actions, noes), (0, [write("Fixture.e", norm(written))], []))
        self.assertRegex(out, r"not filed: Fixture\.triple: .*no item 2")  # the other item was not answered

    def test_answer_never_guesses(self):
        q = self.ask("Fixture.triple", "Fixture.e")  # triple has a review, e has none
        ok = review(says="fine")
        t = lambda *a, **k: item(1, "Fixture.triple", *a, **k)
        e = lambda *a, **k: item(2, "Fixture.e", *a, **k)
        unclosed = f"### 1. Fixture.triple\nCELLS: {ANSWER_CELLS}\nVERDICT: EDIT\nNOTE: n\n~~~review\n{ok}"
        cases = [
            ("an ERROR cell under APPROVE", "Fixture.triple", t("APPROVE", cells=error_cells("junk")), "ERROR"),
            ("an ERROR cell under EDIT", "Fixture.triple", t("EDIT", "NOTE: n", block=ok, cells=error_cells("junk")),
             "ERROR"),
            ("an ERROR cell under WRITE", "Fixture.e", e("WRITE", block=ok, cells=error_cells("junk")), "ERROR"),
            ("a NO with no ERROR cell", "Fixture.triple", t("NO", "CATEGORY: junk   WHY: x"), "ERROR cell"),
            ("a NO of another check than the ERROR cell's", "Fixture.triple",
             t("NO", "CATEGORY: naming   WHY: x", cells=error_cells("junk")), "CATEGORY"),
            ("a NO with a category that is no check", "Fixture.triple",
             t("NO", "CATEGORY: style   WHY: x", cells=error_cells("junk")), "CATEGORY"),
            ("a NO without its WHY", "Fixture.triple", t("NO", "CATEGORY: junk", cells=error_cells("junk")), "WHY"),
            ("a NO without its CATEGORY", "Fixture.triple", t("NO", "WHY: x", cells=error_cells("junk")), "CATEGORY"),
            ("a cell left out", "Fixture.triple", t("APPROVE", cells=ANSWER_CELLS.replace(", naming=checked", "")),
             "missing naming"),
            ("a check twice", "Fixture.triple", t("APPROVE", cells=ANSWER_CELLS + ", junk=checked"), "twice"),
            ("a cell that is no state", "Fixture.triple",
             t("APPROVE", cells=ANSWER_CELLS.replace("junk=checked", "junk=maybe")), "maybe"),
            ("something before the first cell", "Fixture.triple", t("APPROVE", cells="all of them: " + ANSWER_CELLS),
             "CELLS"),
            ("no CELLS line", "Fixture.triple", t("APPROVE", cells=None), "CELLS"),
            ("no VERDICT line", "Fixture.triple", t(None), "VERDICT"),
            ("a verdict that is none of the four", "Fixture.triple", t("MAYBE"), "MAYBE"),
            ("a verdict and more", "Fixture.triple", t("APPROVE, I think"), "VERDICT"),
            ("an APPROVE with a NOTE", "Fixture.triple", t("APPROVE", "NOTE: n"), "NOTE"),
            ("an APPROVE with a text", "Fixture.triple", t("APPROVE", block=ok), "~~~review"),
            ("an EDIT without a NOTE", "Fixture.triple", t("EDIT", block=ok), "NOTE"),
            ("an EDIT with a NOTE that says nothing", "Fixture.triple", t("EDIT", "NOTE:  ", block=ok), "NOTE"),
            ("an EDIT without a text", "Fixture.triple", t("EDIT", "NOTE: n"), "~~~review"),
            ("a text that is not closed", "Fixture.triple", unclosed, "not closed"),
            ("a text without its parts", "Fixture.triple", t("EDIT", "NOTE: n", block="## What it says\nx"),
             "References and tests"),
            ("a text the intake would cut short", "Fixture.triple",
             t("EDIT", "NOTE: n", block=BLOCKS["a command line after a tilde line"][0]), "cut short"),
            ("an edit of nothing", "Fixture.e", e("EDIT", "NOTE: n", block=ok), "WRITE"),
            ("an approval of nothing", "Fixture.e", e("APPROVE"), "WRITE"),
            ("a write over a review", "Fixture.triple", t("WRITE", block=ok), "approve it"),
            ("a write with a NOTE", "Fixture.e", e("WRITE", "NOTE: n", block=ok), "NOTE"),
            ("a write with a DROPPED line", "Fixture.e", e("WRITE", "DROPPED: x — y", block=ok), "DROPPED"),
            ("a write without a text", "Fixture.e", e("WRITE"), "~~~review"),
            ("a DROPPED line with no why", "Fixture.triple", t("EDIT", "NOTE: n", "DROPPED: `x`", block=ok), "DROPPED"),
            ("a verdict whose name is in lower case", "Fixture.triple", t(None, "verdict: APPROVE"), "VERDICT"),
            ("cells whose name is in lower case", "Fixture.triple",
             f"### 1. Fixture.triple\ncells: {ANSWER_CELLS}\nVERDICT: APPROVE\n", "CELLS"),
            ("a reason whose name is in lower case", "Fixture.triple",
             t("NO", "CATEGORY: junk", "Why: x", cells=error_cells("junk")), "WHY"),
            ("a note whose name is in lower case", "Fixture.triple", t("EDIT", "note: n", block=ok), "NOTE"),
            ("a reason in lower case on the line of the category", "Fixture.triple",
             t("NO", "CATEGORY: junk   why: x", cells=error_cells("junk")), "CATEGORY"),
            ("a NO with a text", "Fixture.triple",
             t("NO", "CATEGORY: junk   WHY: x", cells=error_cells("junk"), block=ok), "~~~review"),
        ]
        for why, name, text, needle in cases:
            with self.subTest(why=why):
                code, out, err, actions, noes = self.answer(q, text)
                self.assertEqual(code, 0, err)
                lines = [x for x in out.splitlines() if x.startswith(f"not filed: {name}: ")]
                self.assertEqual(len(lines), 1, out)
                self.assertIn(needle, lines[0])
                self.assertEqual((actions, noes), ([], []))  # and nothing of it was filed

    def test_a_bad_item_does_not_hold_back_a_good_one(self):
        q = self.ask("Fixture.triple", "Fixture.triple_triple")
        code, out, err, actions, noes = self.answer(q, item(1, "Fixture.triple", "MAYBE"),
                                                    item(2, "Fixture.triple_triple", "APPROVE"))
        self.assertEqual((code, actions), (0, [approve("Fixture.triple_triple", V(self.t2))]))
        self.assertRegex(out, r"^not filed: Fixture\.triple: .*MAYBE")

    def test_answer_reads_the_markup_a_model_adds(self):
        q = self.ask("Fixture.triple", "Fixture.triple_triple", "Fixture.e", "Fixture.triple_two")
        edited, written = review(says="triple twice, better"), review(says="e")
        cells = ANSWER_CELLS.replace("object=checked", "Object=Checked").replace("choice=n/a", "choice=na")
        answer = (
            "Here is my review of the three.\r\n\r\n"  # before the first item
            "## 1. `Fixture.triple`\r\n"  # another level of heading, the name in backticks
            f"**CELLS:** {cells}\r\n"  # labels in bold, cells in capitals
            "**VERDICT:** `approve`\r\n\r\n"
            "#### 2. Fixture.triple_triple\r\n"
            f"CELLS: {ANSWER_CELLS}\r\n"
            "VERDICT: **EDIT**\r\n"
            "NOTE: adds the hypothesis the statement skips\r\n"
            "DROPPED:  `Fixture.triple_triple_one`  —  renamed\r\n"
            "~~~review\r\n" + edited.replace("\n", "\r\n") + "~~~\r\n\r\n"
            f"### 3) Fixture.e\r\nCELLS: {ANSWER_CELLS}\r\nVERDICT: WRITE.\r\n"
            "~~~review\r\n" + written.replace("\n", "\r\n") + "~~~\r\n\r\n"
            "---\r\n\r\n"  # a rule between the items
            "### 4. Fixture.triple_two\r\n"
            f"**CELLS:** {error_cells('junk')}\r\n**VERDICT:** NO\r\n"
            "**CATEGORY:** `junk`\r\n**WHY:** `triple 2` is the junk value.\r\n")
        code, out, err, actions, noes = self.answer(q, answer)
        self.assertEqual((code, out), (0, ""), err)
        self.assertEqual(actions, [
            approve("Fixture.triple", V(self.t1)),
            edit("Fixture.triple_triple", V(self.t2), norm(edited),
                 "adds the hypothesis the statement skips",
                 [{"item": "`Fixture.triple_triple_one`", "why": "renamed"}]),
            write("Fixture.e", norm(written))])
        # The reason of a no may come on a line of its own.
        self.assertEqual(noes, [{"decl": "Fixture.triple_two", "category": "junk",
                                 "why": "`triple 2` is the junk value."}])

    def test_a_sentence_after_a_nos_reason_is_not_in_it(self):
        q = self.ask("Fixture.triple", "Fixture.triple_two")
        why, remark = "`triple 0 = 0`, but it should be undefined.", "Let me know if you want me to expand on this."
        for gap in ("\n", ""):  # after a blank line, and on the very next line
            with self.subTest(blank_line=bool(gap)):
                no = item(2, "Fixture.triple_two", "NO", f"CATEGORY: junk   WHY: {why}", cells=error_cells("junk"))
                code, out, err, actions, noes = self.answer(q, item(1, "Fixture.triple", "APPROVE"),
                                                            no.rstrip("\n") + "\n" + gap + remark + "\n")
                self.assertEqual((code, out), (0, ""), err)
                self.assertEqual(actions, [approve("Fixture.triple", V(self.t1))])
                self.assertEqual(noes, [{"decl": "Fixture.triple_two", "category": "junk", "why": why}])

    def test_a_sentence_after_the_last_item_leaves_it_filed(self):
        q = self.ask("Fixture.e", "Fixture.triple")
        written = review(says="e")
        tails = {"after a blank line": "\nLet me know if you want me to expand on this.\n",
                 "on the next line": "Let me know if you want me to expand on this.\n",
                 "after a rule": "---\nI hope this helps.\n",
                 "under a closing heading": "\n### Summary\nBoth items are done.\n"}
        for why, tail in tails.items():
            with self.subTest(why=why):
                last = item(2, "Fixture.triple", "APPROVE").rstrip("\n") + "\n" + tail
                code, out, err, actions, noes = self.answer(q, item(1, "Fixture.e", "WRITE", block=written), last)
                self.assertEqual((code, out), (0, ""), err)
                self.assertEqual(actions, [write("Fixture.e", norm(written)), approve("Fixture.triple", V(self.t1))])

    def test_a_rule_and_a_sentence_between_items_leave_both_filed(self):
        q = self.ask("Fixture.triple_two", "Fixture.triple")
        why = "`triple 2` is the junk value."
        for gap in ("\n", ""):  # with blank lines round the rule and the sentence, and without
            with self.subTest(blank_lines=bool(gap)):
                no = item(1, "Fixture.triple_two", "NO", f"CATEGORY: junk   WHY: {why}", cells=error_cells("junk"))
                between = gap + "---\n" + gap + "I hope this helps.\n" + gap
                code, out, err, actions, noes = self.answer(q, no.rstrip("\n") + "\n", between,
                                                            item(2, "Fixture.triple", "APPROVE"))
                self.assertEqual((code, out), (0, ""), err)
                self.assertEqual(actions, [approve("Fixture.triple", V(self.t1))])
                self.assertEqual(noes, [{"decl": "Fixture.triple_two", "category": "junk", "why": why}])

    def test_prose_that_starts_like_a_field_but_not_in_capitals_is_left_out(self):
        q = self.ask("Fixture.triple", "Fixture.triple_two")
        why = "`triple 2` is the junk value."
        for gap in ("", "\n"):  # under the line, and after a blank line
            with self.subTest(blank_line=bool(gap)):
                yes = item(1, "Fixture.triple", "APPROVE").rstrip("\n") + "\n" + gap
                yes += "Note: this follows the docstring.\n\n"
                no = item(2, "Fixture.triple_two", "NO", f"CATEGORY: junk   WHY: {why}", cells=error_cells("junk"))
                no = no.rstrip("\n") + "\n" + gap + "Note: it is so for every n.\n" + gap
                no += "Why this matters: the junk value is silent.\n"
                code, out, err, actions, noes = self.answer(q, yes, no)
                self.assertEqual((code, out), (0, ""), err)  # not "an APPROVE takes no NOTE", not "a NO takes no NOTE"
                self.assertEqual(actions, [approve("Fixture.triple", V(self.t1))])
                self.assertEqual(noes, [{"decl": "Fixture.triple_two", "category": "junk", "why": why}])

    def test_an_echoed_version_line_is_left_out(self):
        q = self.ask("Fixture.triple")
        echoed = "Version: ffffffffffffffff"
        answer = (f"### 1. Fixture.triple\n{echoed}\nCELLS: {ANSWER_CELLS}\n{echoed}\nVERDICT: APPROVE\n{echoed}\n")
        code, out, err, actions, noes = self.answer(q, answer)
        # Filed with the version the question showed, never the one in the answer.
        self.assertEqual((code, out, actions), (0, "", [approve("Fixture.triple", V(self.t1))]))

    def test_a_stray_line_between_the_fields_does_not_lose_the_item(self):
        q = self.ask("Fixture.triple", "Fixture.triple_triple", "Fixture.e", "Fixture.triple_two")
        edited, written = review(says="triple twice, better"), review(says="e")
        answer = (
            f"### 1. Fixture.triple\nCELLS: {ANSWER_CELLS}\nThis matches the docstring.\nVERDICT: APPROVE\n\n"
            f"### 2. Fixture.triple_triple\nI looked at it again.\nCELLS: {ANSWER_CELLS}\nVERDICT: EDIT\n"
            "Here is what it lacks:\nNOTE: says more\nIt keeps every bullet.\n"
            f"~~~review\n{edited}~~~\nThat is the new text.\n\n"
            f"### 3. Fixture.e\nCELLS: {ANSWER_CELLS}\n---\nVERDICT: WRITE\n~~~review\n{written}~~~\n\n"
            f"### 4. Fixture.triple_two\nCELLS: {error_cells('junk')}\nVERDICT: NO\nThe error is clear.\n"
            "CATEGORY: junk   WHY: it is junk.\n")
        code, out, err, actions, noes = self.answer(q, answer)
        self.assertEqual((code, out), (0, ""), err)
        self.assertEqual(actions, [approve("Fixture.triple", V(self.t1)),
                                   edit("Fixture.triple_triple", V(self.t2), norm(edited), "says more"),
                                   write("Fixture.e", norm(written))])
        self.assertEqual(noes, [{"decl": "Fixture.triple_two", "category": "junk", "why": "it is junk."}])

    def test_a_field_is_one_line_with_its_name_in_capitals(self):
        q = self.ask("Fixture.triple_triple", "Fixture.triple_two", "Fixture.triple")
        edited = review(says="triple twice, better")
        answer = (
            f"### 1. Fixture.triple_triple\nCELLS: {ANSWER_CELLS}\nVERDICT: EDIT\nNOTE: adds the hypothesis\n"
            "  the statement skips\nDROPPED: `x` — renamed\nin Tau Ceti\n"
            f"~~~review\n{edited}~~~\n\n"
            f"### 2. Fixture.triple_two\nCELLS: {error_cells('junk')}\nVERDICT: NO\n"
            "CATEGORY: junk   WHY: the first line\nand the second\n\n"
            f"### 3. Fixture.triple\nCELLS: {ANSWER_CELLS}\nverdict: APPROVE\n")
        code, out, err, actions, noes = self.answer(q, answer)
        self.assertEqual(code, 0, err)
        # What goes on over the next line is not the field's: not a note's, a dropped item's, or a reason's.
        self.assertEqual(actions, [edit("Fixture.triple_triple", V(self.t2), norm(edited), "adds the hypothesis",
                                        [{"item": "`x`", "why": "renamed"}])])
        self.assertEqual(noes, [{"decl": "Fixture.triple_two", "category": "junk", "why": "the first line"}])
        # And a name in lower case is no field: the verdict of the third is missing, and it says so.
        self.assertEqual(out.splitlines(), ["not filed: Fixture.triple: no VERDICT line: APPROVE, EDIT, WRITE or NO"])

    def test_answer_may_come_in_a_code_block_with_rules_between_its_items(self):
        q = self.ask("Fixture.triple", "Fixture.e")
        written = review(says="e")
        code, out, err, actions, noes = self.answer(
            q, "```markdown\n", item(1, "Fixture.triple", "APPROVE"), "---\n\n",
            item(2, "Fixture.e", "WRITE", block=written), "```\n")
        self.assertEqual((code, out), (0, ""), err)
        self.assertEqual(actions, [approve("Fixture.triple", V(self.t1)), write("Fixture.e", norm(written))])

    def test_answer_reads_an_error_cell_that_has_commas(self):
        q = self.ask("Fixture.triple")
        cells = error_cells("edge-cases", "the statement says `n < 3`, where the source says `n ≤ 3`, so 3 is left out")
        code, out, err, actions, noes = self.answer(q, item(1, "Fixture.triple", "NO", "CATEGORY: edge-cases   WHY: x",
                                                            cells=cells))
        # The WHY of the item is the reason of the no, not the cell's.
        self.assertEqual((code, out, noes), (0, "", [{"decl": "Fixture.triple", "category": "edge-cases", "why": "x"}]))

    def test_answer_leaves_out_a_text_no_comment_could_hold(self):
        # `post` refuses a whole file for one action longer than a comment, so the answer does not hand it one.
        q = self.ask("Fixture.triple", "Fixture.triple_triple")
        huge = review(says="x" * review_site.COMMENT_CAP)
        code, out, err, actions, noes = self.answer(q, item(1, "Fixture.triple", "EDIT", "NOTE: n", block=huge),
                                                    item(2, "Fixture.triple_triple", "APPROVE"))
        self.assertEqual(actions, [approve("Fixture.triple_triple", V(self.t2))])
        self.assertRegex(out, r"^not filed: Fixture\.triple: .*characters, and a comment holds 60,000")

    def test_answer_keeps_a_review_whole(self):
        q = self.ask("Fixture.triple")
        for why, (text, whole) in BLOCKS.items():
            with self.subTest(why=why):
                code, out, err, actions, noes = self.answer(q, item(1, "Fixture.triple", "EDIT", "NOTE: n", block=text))
                self.assertEqual(code, 0, err)
                if whole:  # the text reaches `post` as it was, whatever fences and lines it holds
                    self.assertEqual(actions, [edit("Fixture.triple", V(self.t1), norm(text), "n")])
                else:
                    self.assertEqual(actions, [])
                    self.assertRegex(out, r"^not filed: Fixture\.triple: .*cut short")
        # A heading like an item's inside the text is the text's, not an item's.
        text = review(says="### 3. Something\nlooks like an item, and is not")
        code, out, err, actions, noes = self.answer(q, item(1, "Fixture.triple", "EDIT", "NOTE: n", block=text))
        self.assertEqual((out, actions), ("", [edit("Fixture.triple", V(self.t1), norm(text), "n")]))

    def test_answer_matches_items_by_number_and_name(self):
        q = self.ask("Fixture.triple", "Fixture.triple_triple", "Fixture.e")
        code, out, err, actions, noes = self.answer(
            q, item(1, "Fixture.triple", "APPROVE"),
            item(9, "Fixture.nope", "APPROVE"),  # a name that is not in the question
            item(2, "Fixture.e", "WRITE", block=review()),  # the question's item 2 is another
            item(5, "Fixture.triple_triple", "APPROVE"))  # and this one's number is 2
        self.assertEqual((code, actions), (0, [approve("Fixture.triple", V(self.t1))]))
        for want in (r"not filed: Fixture\.nope: .*not in the question",
                     r"not filed: Fixture\.e: .*item 2 .*Fixture\.triple_triple",
                     r"not filed: Fixture\.triple_triple: .*numbers it 2",
                     r"not filed: Fixture\.triple_triple: .*no item 2",  # nothing answered item 2 of the question
                     r"not filed: Fixture\.e: .*no item 3"):
            self.assertRegex(out, want)
        self.assertNotIn("not filed: Fixture.triple:", out)
        # An item twice is not guessed at: neither is filed.
        code, out, err, actions, noes = self.answer(q, item(1, "Fixture.triple", "APPROVE"),
                                                    item(1, "Fixture.triple", "APPROVE"))
        self.assertEqual(actions, [])
        self.assertRegex(out, r"not filed: Fixture\.triple: .*item 1 .*twice")

    def test_the_instructions_examples_are_answers_it_reads(self):
        # The format the instructions show Astra is the format the answer is read in: each of their examples, given a
        # heading of the question (a declaration with a review for the first two, none for the third), is filed as
        # what it says.
        names = ["Fixture.triple", "Fixture.triple_triple", "Fixture.e", "Fixture.triple_two"]
        q = self.ask(*names)
        head = Path(q).read_text(encoding="utf-8").split(self.GUIDE.strip())[0]
        examples = re.findall(r"(?ms)^```\n### [^\n]*\n(.*?)^```$", head)
        self.assertEqual([re.search(r"^VERDICT: (\w+)", x, re.M)[1] for x in examples],
                         ["APPROVE", "EDIT", "WRITE", "NO"])
        code, out, err, actions, noes = self.answer(
            q, *(f"### {k}. {name}\n{body}\n" for k, (name, body) in enumerate(zip(names, examples), 1)))
        self.assertEqual((code, out), (0, ""), err)
        self.assertEqual([next(iter(a)) for a in actions], ["approve", "edit", "write"])
        self.assertEqual([n["decl"] for n in noes], ["Fixture.triple_two"])
        self.assertIn(noes[0]["category"], AXES)

    def test_what_astra_answer_writes_is_what_post_takes(self):
        # Voyager's drafts are posted first and the site does not show them yet: Astra approves the one, and edits the
        # other, of the texts the question showed, and `post` takes both against the drafts, as well as an edit of the
        # site's own text.
        draft, drafted_d = review(says="e, as Voyager wrote it"), review(says="d, as Voyager edited it")
        drafts = self.jsonl(write("Fixture.e", draft), edit("Fixture.d", V(self.t4), drafted_d, "says more"),
                            name="voyager.jsonl")
        q = self.ask("Fixture.triple", "Fixture.triple_triple", "Fixture.e", "Fixture.d", drafts=drafts)
        edited, redrafted = review(says="triple twice, said better"), review(says="d, edited again")
        actions = self.dir / "actions.jsonl"
        code, out, err, rows, noes = self.answer(
            q, item(1, "Fixture.triple", "APPROVE"),
            item(2, "Fixture.triple_triple", "EDIT", "NOTE: says it better",
                 "DROPPED: `Fixture.triple_triple_one` — renamed", block=edited),
            item(3, "Fixture.e", "APPROVE"), item(4, "Fixture.d", "EDIT", "NOTE: and again", block=redrafted))
        self.assertEqual((code, out), (0, ""), err)
        self.assertEqual(rows[2], approve("Fixture.e", V(draft)))
        self.assertEqual(rows[3], edit("Fixture.d", V(drafted_d), norm(redrafted), "and again"))
        code, out, err = self.cli("post", str(actions), "--agent", "Codex, GPT-6 Astra", "--commit", self.commit[:12],
                                  "--drafts", drafts, "--dry-run")
        self.assertEqual(code, 0, err)
        for line in (f"Approve: Fixture.triple — {V(self.t1)} — {CELLS_LINE}",
                     f"Edit: Fixture.triple_triple — {V(self.t2)} — {CELLS_LINE} — says it better",
                     "Dropped: `Fixture.triple_triple_one` — renamed",
                     f"Approve: Fixture.e — {V(draft)} — {CELLS_LINE}",
                     f"Edit: Fixture.d — {V(drafted_d)} — {CELLS_LINE} — and again"):
            self.assertIn(line, out)
        self.assertIn(norm(edited), out)
        self.assertIn(norm(redrafted), out)
        # Without the drafts, `post` refuses them: the versions are the drafts', which the site does not show.
        code, out, err = self.cli("post", str(actions), "--agent", "Codex, GPT-6 Astra", "--commit", self.commit[:12],
                                  "--dry-run")
        self.assertEqual(code, 1)
        self.assertIn("no draft is given", err)  # for the approval of e
        self.assertIn(V(drafted_d), err)  # for the edit of d: the version it names is not the site's

    def test_answer_usage_errors(self):
        q = self.ask("Fixture.triple")
        good = self.dir / "good.md"
        good.write_text(item(1, "Fixture.triple", "APPROVE"), encoding="utf-8")
        empty, not_a_question, odd_question = (self.dir / x for x in ("empty.md", "not_a_question.txt", "odd.txt"))
        empty.write_text("\n \n", encoding="utf-8")
        not_a_question.write_text("Review these.\n\n### 1. Fixture.triple\n", encoding="utf-8")
        odd_question.write_text('<!-- astra-question {"items": 3} -->\n', encoding="utf-8")
        here, there = ["--out", str(self.dir / "o.jsonl"), "--noes", str(self.dir / "n.jsonl")], \
            ["--out", str(self.dir / "no" / "o.jsonl"), "--noes", str(self.dir / "n.jsonl")]
        cases = {"no answer file": [str(self.dir / "no.md"), "--question", q, *here],
                 "an empty answer": [str(empty), "--question", q, *here],
                 "no question file": [str(good), "--question", str(self.dir / "no.txt"), *here],
                 "a question that is none": [str(good), "--question", str(not_a_question), *here],
                 "a question whose items are none": [str(good), "--question", str(odd_question), *here],
                 "files it cannot write": [str(good), "--question", q, *there]}
        for why, argv in cases.items():
            with self.subTest(why=why):
                code, out, err = self.cli("astra-answer", *argv)
                self.assertEqual((code, out), (2, ""), err)
                self.assertTrue(err.startswith("error:"), err)
        self.assertFalse((self.dir / "o.jsonl").exists())
        self.assertFalse((self.dir / "n.jsonl").exists())
        for argv in (["astra-answer", str(good), "--question", q, "--out", "x"],  # --noes
                     ["astra-answer", str(good), "--out", "x", "--noes", "y"]):  # --question
            with self.subTest(argv=argv[-2]):
                self.assertEqual(self.cli(*argv)[0], 2)

    def test_both_commands_are_in_the_help(self):
        code, out, err = self.cli("--help")
        self.assertEqual((code, err), (0, ""))
        for want in ("astra-question NAME... --tauceti", "astra-answer ANSWER --question"):
            self.assertIn(want, out)


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
