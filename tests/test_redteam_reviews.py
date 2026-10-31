"""Tests of scripts/redteam.py's reviews on the Tau Ceti review site: the `yes` of an audit (R6 step 8), `reviews`, which
posts them once the site shows the file as audited (R6 step 10), and `yes`, which records a re-review (R0).

`reviews` runs scripts/review_site.py for what the site shows and to post. Here `redteam.run` runs that script's own
`main` in this process, against a fake site (`review_site.get`) and a fake GitHub (`review_site.gh`), so what `reviews`
hands it is checked by the real `post`. The Tau Ceti checkout is a real git repository in a temporary directory, and the
ledger a temporary directory ($REDTEAM_LEDGER): nothing here touches the network or GitHub, and nothing but git runs.

Run them from the root of the repository: python3 -m unittest discover -s tests
"""
import contextlib
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "scripts"))
import redteam  # noqa: E402
import review_site  # noqa: E402

#: The real `subprocess.run`, taken before any test patches it: git runs with it.
REAL_RUN = subprocess.run
#: The environment git gets: none of git's own variables (`GIT_DIR`, ... when a hook runs the tests), which would point
#: it at another repository.
GIT_ENV = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
OWNER = "host-1"
MODEL = "claude-opus-5-5"
AXES = ["object", "convention", "edge-cases", "junk", "vacuous", "choice", "generality", "naming"]
CELLS = {**dict.fromkeys(AXES, "checked"), "choice": "na"}
CELLS_LINE = "object, convention, edge-cases, junk, vacuous, choice n/a, generality, naming"
CATEGORIES = ["correctness", "generality", "reuse", "proof", "naming", "api", "docs", "hygiene"]
FILE = "TauCeti/Foo.lean"
SOURCE = """\
namespace TauCeti.Foo

/-- One. -/
def one : Nat := 1

/-- One and one make two. -/
theorem two : one + one = 2 := rfl

/-- Three ones make three. -/
theorem three : one + one + one = 3 := rfl

/-- Four ones make four. -/
theorem four : one + one + one + one = 4 := rfl

end TauCeti.Foo
"""
OTHER = "namespace TauCeti.Other\n\n/-- Zero. -/\ndef zero : Nat := 0\n\nend TauCeti.Other\n"
NAMES = ["TauCeti.Foo.one", "TauCeti.Foo.two", "TauCeti.Foo.three", "TauCeti.Foo.four"]
#: The audit's matrix: every declaration of FILE, and the file's own row, ok in every category.
MATRIX = {name: dict.fromkeys(CATEGORIES, "ok") for name in ["(file)", *NAMES]}


def review(says):
    """A standard review's text, in its three parts."""
    return f"## What it says\n{says}\n\n## References and tests\n- Fixture documentation, §1.\n\n## Lean subtleties\nNone.\n"


TEXT_ONE = review("`TauCeti.Foo.one` is the natural number $1$.")
TEXT_TWO = review("`TauCeti.Foo.two` says that $1 + 1 = 2$.")
TEXT_THREE = review("`TauCeti.Foo.three` says that $1 + 1 + 1 = 3$.")
TEXT_FOUR = review("`TauCeti.Foo.four` says that $1 + 1 + 1 + 1 = 4$.")
EDIT_THREE = review("`TauCeti.Foo.three` says that $1 + 1 + 1 = 3$ in the natural numbers, where `one` is $1$.")
#: The version of a text the site no longer shows.
STALE = review_site.version_of(review("An earlier text."))


def entry(text):
    """A declaration's entry in its shard of standard/<k>.json, as the site builds it."""
    by = {"kind": "agent", "login": "cb", "agent": {"tool": "Voyager", "model": "claude-fable-5-1"},
          "label": "Voyager (claude-fable-5-1)", "involvement": "unknown"}
    return {"text": text, "version": review_site.version_of(text), "at": "2026-10-30T10:00:00Z", "by": by,
            "approving": True, "url": "https://github.com/o/r/issues/1#issuecomment-901", "current": True,
            "approvers": [], "earlier": 0}


class Site:
    """The review site's data, as `review_site.get` reads it: Tau Ceti at ``commit``, whose module TauCeti.Foo, the file
    FILE, has the declarations ``names``, and the standard review of each that has one (``reviews``, by name)."""
    SHARDS = {"names": 4, "nodes": 4, "standard": 8}

    def __init__(self, commit, names=NAMES):
        self.commit, self.names, self.reviews = commit, list(names), {}

    def get(self, path):
        if path == "meta.json":
            return {"library": {"commit": self.commit}, "shards": dict(self.SHARDS), "store": {"bulk": 1},
                    "review": {"outside": ["Mathlib"]}}
        kind, k = path.removesuffix(".json").split("/")
        k = int(k)
        if kind == "names":
            return [[i, n] for i, n in enumerate(self.names) if review_site.fnv(n, self.SHARDS["names"]) == k]
        if kind == "nodes":
            n = self.SHARDS["nodes"]
            return [[name, "t", 1, 0, "", 0, 0, [], [], 0] for name in self.names[k * n:(k + 1) * n]]
        if kind == "m" and k == 0:
            return {"name": "TauCeti.Foo", "path": FILE,
                    "decls": [{"id": i, "name": name, "k": "t", "records": []} for i, name in enumerate(self.names)]}
        if kind == "standard":
            return {name: r for name, r in self.reviews.items() if review_site.fnv(name, self.SHARDS["standard"]) == k}
        raise AssertionError(f"the site was asked for {path}")


class Gh:
    """GitHub's `gh`, as `review_site.gh` calls it: it records each comment it is asked to post, or fails as gh does."""

    def __init__(self):
        self.bodies, self.fail = [], False

    def __call__(self, *args, body=None):
        if self.fail:
            review_site.die("error: gh issue comment: HTTP 502", 2)
        self.bodies.append(body)
        return f"https://github.com/{review_site.REPO}/issues/1#issuecomment-{len(self.bodies)}"


class Case(unittest.TestCase):
    """A Tau Ceti checkout with three commits: c1 without FILE, c2 that adds it (the commit audited), and c3 that changes
    it; a site at c2, with standard reviews of one, three and four; and an empty ledger."""

    def setUp(self):
        if shutil.which("git") is None:
            self.skipTest("git is not installed")
        self.dir = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.dir)
        self.repo, self.ledger = self.dir / "TauCeti", self.dir / "ledger"
        self.c1 = self.commit_files({"TauCeti/Other.lean": OTHER})
        self.c2 = self.commit_files({FILE: SOURCE})
        self.c3 = self.commit_files({FILE: SOURCE.replace("= 3 := rfl", "= 3 := by rfl")})
        self.site, self.gh, self.posts = Site(self.c2), Gh(), []
        self.site.reviews = {"TauCeti.Foo.one": entry(TEXT_ONE), "TauCeti.Foo.three": entry(TEXT_THREE),
                             "TauCeti.Foo.four": entry(TEXT_FOUR)}
        env = {"REDTEAM_LEDGER": str(self.ledger), "REDTEAM_OWNER": OWNER}
        # Whatever the fake `run` does not take does not reach the network or run a program.
        for patcher in (mock.patch.dict(os.environ, env), mock.patch.object(redteam, "run", self.fake_run),
                        mock.patch.object(subprocess, "run", side_effect=AssertionError("unexpected call of run")),
                        mock.patch.object(review_site.urllib.request, "urlopen",
                                          side_effect=AssertionError("unexpected call of urlopen"))):
            patcher.start()
            self.addCleanup(patcher.stop)

    def git(self, *args):
        done = REAL_RUN(["git", "-C", str(self.repo), "-c", "user.name=T", "-c", "user.email=t@example.org", "-c",
                         "commit.gpgsign=false", "-c", "core.autocrlf=false", "-c", f"core.hooksPath={os.devnull}",
                         *args], capture_output=True, text=True, env=GIT_ENV)
        self.assertEqual(done.returncode, 0, done.stderr)
        return done.stdout.strip()

    def commit_files(self, files):
        """Commits ``files`` (path to text) to the checkout, which is made if need be: the new commit."""
        self.repo.mkdir(exist_ok=True)
        if not (self.repo / ".git").exists():
            self.git("init", "-q")
        for path, text in files.items():
            (self.repo / path).parent.mkdir(parents=True, exist_ok=True)
            (self.repo / path).write_text(text, encoding="utf-8")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "fixture")
        return self.git("rev-parse", "HEAD")

    def fake_run(self, cmd, cwd=None, check=True, env=None):
        """`redteam.run`: review_site.py's `main` in this process against the fake site and GitHub, recording what each
        `post` is given; git as it is."""
        if list(cmd[:2]) == [sys.executable, redteam.REVIEW_SITE]:
            argv = list(cmd[2:])
            if argv[0] == "post":
                with open(argv[1], encoding="utf-8") as f:
                    actions = [json.loads(line) for line in f if line.strip()]
                self.posts.append({"actions": actions, "options": dict(zip(argv[2::2], argv[3::2]))})
            out, err, code = io.StringIO(), io.StringIO(), 0
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err), \
                    mock.patch.object(review_site, "get", self.site.get), mock.patch.object(review_site, "gh", self.gh):
                try:
                    review_site.main(argv)
                except SystemExit as e:
                    code = 0 if e.code is None else e.code if isinstance(e.code, int) else 1
            done = subprocess.CompletedProcess(cmd, code, out.getvalue(), err.getvalue())
        elif cmd[0] == "git":
            done = REAL_RUN(cmd, cwd=cwd, capture_output=True, text=True, env=env or GIT_ENV)
        else:
            raise AssertionError(f"unexpected call of run: {cmd}")
        if check and done.returncode != 0:
            redteam.die("command failed: %s\n%s" % (" ".join(cmd), done.stderr.strip()))
        return done

    def cli(self, *argv):
        """(exit code, stdout, stderr) of `redteam.py --repo <the checkout> ARGV`."""
        out, err, code = io.StringIO(), io.StringIO(), 0
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err), \
                mock.patch.object(sys, "argv", ["redteam.py", "--repo", str(self.repo), *argv]):
            try:
                redteam.main()
            except SystemExit as e:
                code = e.code
        return code, out.getvalue(), err.getvalue()

    def json_file(self, value, name="input.json"):
        """``value`` as a JSON file, as `@path` for the command line."""
        path = self.dir / name
        path.write_text(json.dumps(value, ensure_ascii=False), encoding="utf-8")
        return "@" + str(path)

    def audit(self, yes):
        """Records the audit of FILE at c2, with every declaration ok, the model MODEL and ``yes``."""
        code, out, err = self.cli("audit", self.json_file({"file": FILE, "matrix": MATRIX, "model": MODEL, "yes": yes}),
                                  "--ref", self.c2)
        self.assertEqual(code, 0, err)

    def append(self, sub, row):
        """Appends ``row`` to this agent's file of the ledger's ``sub``, as an earlier version of redteam.py did."""
        (self.ledger / sub).mkdir(parents=True, exist_ok=True)
        with open(self.ledger / sub / f"{OWNER}.jsonl", "a", encoding="utf-8") as f:
            f.write(json.dumps(row) + "\n")

    def old_audit(self, yes):
        """An audit of FILE at c2 as redteam.py recorded it before 0.82.0, its yes a map of names to reasons."""
        self.append("audits", {"file": FILE, "matrix": MATRIX, "model": MODEL, "yes": yes,
                               "blob": self.git("rev-parse", f"{self.c2}:{FILE}"), "main": self.c2,
                               "audited_at": "2026-10-29T10:00:00Z", "owner": OWNER, "decls": 4, "findings": []})

    def rows(self, sub="reviews"):
        """This agent's rows of the ledger's ``sub``, in the order written."""
        path = self.ledger / sub / f"{OWNER}.jsonl"
        if not path.exists():
            return []
        return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]

    def states(self):
        """{(state, name)} over the declarations the reviews ledger names."""
        return {(row["state"], name) for row in self.rows() for name in row.get("decls", [])}

    def version(self, name):
        """The version of the standard review the site shows for ``name``."""
        return self.site.reviews[name]["version"]


class YesTests(Case):
    def test_yes_needs_cells_and_one_decision(self):
        known = {"RT-1": {"id": "RT-1", "severity": "MINOR", "status": "confirmed"},
                 "RT-2": {"id": "RT-2", "severity": "CRITICAL", "status": "confirmed"}}
        matrix = {**MATRIX, "TauCeti.Foo.two": {**MATRIX["TauCeti.Foo.two"], "correctness": "F:RT-1"},
                  "TauCeti.Foo.three": {**MATRIX["TauCeti.Foo.three"], "naming": "F:RT-2"}}
        version = "dd83c85a488e22c8"
        good = {
            "an approval": {"cells": CELLS, "approve": version},
            "an approval by 8 digits": {"cells": CELLS, "approve": version[:8]},
            "an approval with n/a": {"cells": {**CELLS, "junk": "n/a"}, "approve": version},
            "a write": {"cells": CELLS, "write": TEXT_ONE},
            "an edit": {"cells": CELLS, "edit": version, "note": "adds the value", "dropped": [], "text": TEXT_ONE},
            "an edit that drops a reference": {"cells": CELLS, "edit": version, "note": "drops a dead reference",
                                               "dropped": [{"item": "Fixture documentation", "why": "gone"}],
                                               "text": TEXT_ONE},
            "an edit without dropped": {"cells": CELLS, "edit": version, "note": "adds the value", "text": TEXT_ONE},
        }
        for what, e in good.items():
            with self.subTest(what):
                self.assertEqual(redteam.yes_problems({"model": MODEL, "yes": {"TauCeti.Foo.one": e}}, MATRIX, {}),
                                 [])
        without_junk = {a: s for a, s in CELLS.items() if a != "junk"}
        bad = {
            "no cells": {"approve": version},
            "seven cells": {"cells": without_junk, "approve": version},
            "a cell neither checked nor na": {"cells": {**CELLS, "junk": "ok"}, "approve": version},
            "a cell that is no check of the site's": {"cells": {**CELLS, "proof": "checked"}, "approve": version},
            "no decision": {"cells": CELLS},
            "two decisions": {"cells": CELLS, "approve": version, "write": TEXT_ONE},
            "all three decisions": {"cells": CELLS, "approve": version, "write": TEXT_ONE, "edit": version,
                                    "note": "x", "text": TEXT_ONE},
            "a write without the headings": {"cells": CELLS, "write": "`one` is $1$."},
            "a write without its last part": {"cells": CELLS, "write": TEXT_ONE.split("## Lean subtleties")[0]},
            "a write with its parts out of order": {
                "cells": CELLS, "write": "## References and tests\n- A.\n\n## What it says\nX.\n\n## Lean subtleties\n"
                                         "None.\n"},
            "an edit without the headings": {"cells": CELLS, "edit": version, "note": "x", "text": "`one` is $1$."},
            "an edit without its text": {"cells": CELLS, "edit": version, "note": "x"},
            "an edit without a note": {"cells": CELLS, "edit": version, "text": TEXT_ONE},
            "a drop without why": {"cells": CELLS, "edit": version, "note": "x", "dropped": [{"item": "A"}],
                                   "text": TEXT_ONE},
            "an approval of no version": {"cells": CELLS, "approve": "latest"},
            "an approval of too short a version": {"cells": CELLS, "approve": version[:7]},
            "a key an approval does not have": {"cells": CELLS, "approve": version, "note": "x"},
            "a key a write does not have": {"cells": CELLS, "write": TEXT_ONE, "text": TEXT_ONE},
            "reasons, the form before": "Correctly stated: `one` is 1.",
            "no reasons, the form before": "",
        }
        for what, e in bad.items():
            with self.subTest(what):
                problems = redteam.yes_problems({"model": MODEL, "yes": {"TauCeti.Foo.one": e}}, MATRIX, {})
                self.assertNotEqual(problems, [])
                self.assertTrue(all("TauCeti.Foo.one" in p for p in problems), problems)
        # And what it refused before: a declaration the audit does not have, one whose correctness check failed or
        # against which a CRITICAL finding stands, a name that is not a full name, and a model that is missing or a
        # family.
        fine = {"cells": CELLS, "approve": version}
        for what, row in {"not in the matrix": {"model": MODEL, "yes": {"TauCeti.Foo.five": fine}},
                          "correctness failed": {"model": MODEL, "yes": {"TauCeti.Foo.two": fine}},
                          "a CRITICAL finding": {"model": MODEL, "yes": {"TauCeti.Foo.three": fine}},
                          "not a full name": {"model": MODEL, "yes": {"TauCeti.Foo one": fine}},
                          "no model": {"yes": {"TauCeti.Foo.one": fine}},
                          "a family": {"model": "Opus", "yes": {"TauCeti.Foo.one": fine}},
                          "not a map": {"model": MODEL, "yes": ["TauCeti.Foo.one"]}}.items():
            with self.subTest(what):
                self.assertNotEqual(redteam.yes_problems(row, matrix, known), [])
        self.assertEqual(redteam.yes_problems({"model": MODEL, "yes": {"TauCeti.Foo.four": fine}}, matrix, known), [])

    def test_no_review_over_a_finding_a_site_check_covers(self):
        # The site's checks cover the audit's correctness findings (object ... choice), its generality findings
        # (generality), and its naming and docs findings (naming). With one standing that check fails, a failed check
        # has no cell, and the red team leaves no no: the declaration gets no review until a later audit finds it clean.
        fine = {"cells": CELLS, "approve": "dd83c85a488e22c8"}

        def finding(category, status, severity="MINOR"):
            return {"id": "RT-1", "category": category, "severity": severity, "status": status}

        cases = {  # what: (the column of the matrix that cites it, the finding, whether the review is refused)
            "a generality finding": ("generality", finding("generality", "confirmed"), True),
            "a MAJOR generality finding in a PR": ("generality", finding("generality", "pr-open", "MAJOR"), True),
            "a naming finding": ("naming", finding("naming", "confirmed"), True),
            "a docs finding": ("docs", finding("docs", "confirmed"), True),
            "a suspected docs finding": ("docs", finding("docs", "suspected"), True),
            "a naming finding whose fix landed": ("naming", finding("naming", "landed"), True),
            "a correctness finding another check cites": ("api", finding("correctness", "confirmed"), True),
            "a reuse finding the naming check cites": ("naming", finding("reuse", "confirmed", "MAJOR"), True),
            "a refuted generality finding": ("generality", finding("generality", "refuted"), False),
            "a reuse finding": ("reuse", finding("reuse", "confirmed", "MAJOR"), False),
            "a proof finding": ("proof", finding("proof", "confirmed"), False),
            "an api finding": ("api", finding("api", "confirmed"), False),
            "a hygiene finding": ("hygiene", finding("hygiene", "confirmed", "NIT"), False),
        }
        for what, (column, f, refused) in cases.items():
            with self.subTest(what):
                matrix = {**MATRIX, "TauCeti.Foo.one": {**MATRIX["TauCeti.Foo.one"], column: "F:RT-1"}}
                problems = redteam.yes_problems({"model": MODEL, "yes": {"TauCeti.Foo.one": fine}}, matrix,
                                                {"RT-1": f})
                self.assertEqual(problems != [], refused, problems)
                self.assertTrue(all("TauCeti.Foo.one" in p for p in problems), problems)

    def test_the_audit_refuses_a_review_over_a_finding_of_the_ledger(self):
        f = {"id": "RT-20261031-a1b2c3", "file": FILE, "decl": "TauCeti.Foo.two", "category": "generality",
             "severity": "MINOR", "status": "confirmed", "claim": "the hypothesis `h` is never used",
             "pattern": "redundant-hypothesis", "rubric": "generality"}
        code, out, err = self.cli("finding", self.json_file(f, "finding.json"))
        self.assertEqual(code, 0, err)
        matrix = {**MATRIX, "TauCeti.Foo.two": {**MATRIX["TauCeti.Foo.two"], "generality": "F:" + f["id"]}}
        fine = {"cells": CELLS, "approve": "dd83c85a488e22c8"}
        code, out, err = self.cli("audit", self.json_file({"file": FILE, "matrix": matrix, "model": MODEL,
                                                           "yes": {"TauCeti.Foo.two": fine}}), "--ref", self.c2)
        self.assertEqual(code, 1)
        self.assertIn("TauCeti.Foo.two", err)
        self.assertEqual(self.rows("audits"), [])
        code, out, err = self.cli("audit", self.json_file({"file": FILE, "matrix": matrix, "model": MODEL,
                                                           "yes": {"TauCeti.Foo.one": fine}}), "--ref", self.c2)
        self.assertEqual(code, 0, err)

    def test_the_audit_refuses_a_yes_it_could_not_post(self):
        for yes in ({"TauCeti.Foo.one": "Correctly stated."},
                    {"TauCeti.Foo.one": {"cells": {a: s for a, s in CELLS.items() if a != "naming"},
                                         "approve": self.version("TauCeti.Foo.one")}}):
            with self.subTest(yes=yes):
                code, out, err = self.cli("audit", self.json_file({"file": FILE, "matrix": MATRIX, "model": MODEL,
                                                                   "yes": yes}), "--ref", self.c2)
                self.assertEqual(code, 1)
                self.assertIn("TauCeti.Foo.one", err)
                self.assertEqual(self.rows("audits"), [])


class ReviewsTests(Case):
    def test_reviews_posts_actions_for_a_file_the_site_shows(self):
        v_one, v_three = self.version("TauCeti.Foo.one"), self.version("TauCeti.Foo.three")
        self.audit({"TauCeti.Foo.one": {"cells": CELLS, "approve": v_one},
                    "TauCeti.Foo.two": {"cells": CELLS, "write": TEXT_TWO},
                    "TauCeti.Foo.three": {"cells": CELLS, "edit": v_three[:8], "note": "says where the sum is taken",
                                          "text": EDIT_THREE}})
        code, out, err = self.cli("reviews")
        self.assertEqual(code, 0, err)
        [post] = self.posts
        self.assertEqual(post["actions"], [
            {"approve": "TauCeti.Foo.one", "version": v_one, "cells": CELLS},
            {"edit": "TauCeti.Foo.three", "parent": v_three[:8], "cells": CELLS, "note": "says where the sum is taken",
             "dropped": [], "text": EDIT_THREE},
            {"write": "TauCeti.Foo.two", "cells": CELLS, "text": TEXT_TWO}])
        self.assertEqual(post["options"]["--commit"], self.c2)
        self.assertEqual(post["options"]["--agent"], f"Tau Ceti red team, {MODEL}, session {OWNER}")
        [body] = self.gh.bodies
        lines = body.splitlines()
        self.assertEqual(lines[:2], [f"<!-- agent: tool=Tau Ceti red team; model={MODEL}; session={OWNER} -->",
                                     f"Red-team audit of {FILE} at Tau Ceti {self.c2[:12]}."])
        self.assertIn(f"Approve: TauCeti.Foo.one — {v_one} — {CELLS_LINE}", lines)
        self.assertIn(f"Edit: TauCeti.Foo.three — {v_three[:8]} — {CELLS_LINE} — says where the sum is taken", lines)
        self.assertIn(f"Write: TauCeti.Foo.two — {CELLS_LINE}", lines)
        self.assertEqual([(r["state"], r["site"], r["decls"]) for r in self.rows()],
                         [("posted", self.c2, ["TauCeti.Foo.one", "TauCeti.Foo.three", "TauCeti.Foo.two"])])
        # A later round posts nothing more.
        self.assertEqual(self.cli("reviews")[0], 0)
        self.assertEqual((len(self.gh.bodies), len(self.rows())), (1, 1))

    def test_a_changed_review_waits_for_re_review(self):
        self.audit({"TauCeti.Foo.one": {"cells": CELLS, "approve": STALE},  # its text has changed since
                    "TauCeti.Foo.two": {"cells": CELLS, "write": TEXT_TWO},  # another agent wrote one since (below)
                    "TauCeti.Foo.three": {"cells": CELLS, "edit": STALE, "note": "says where the sum is taken",
                                          "text": EDIT_THREE},  # the text it edits has changed since
                    "TauCeti.Foo.four": {"cells": CELLS, "approve": self.version("TauCeti.Foo.four")}})
        self.site.reviews["TauCeti.Foo.two"] = entry(review("Written by another agent after the audit."))
        code, out, err = self.cli("reviews")
        self.assertEqual(code, 0, err)
        [post] = self.posts
        self.assertEqual(post["actions"], [{"approve": "TauCeti.Foo.four", "version": self.version("TauCeti.Foo.four"),
                                            "cells": CELLS}])
        self.assertEqual(self.states(), {("posted", "TauCeti.Foo.four"), ("re-review", "TauCeti.Foo.one"),
                                         ("re-review", "TauCeti.Foo.two"), ("re-review", "TauCeti.Foo.three")})
        for name in ("TauCeti.Foo.one", "TauCeti.Foo.two", "TauCeti.Foo.three"):
            self.assertIn(name, out)
        # They wait for the re-review: a later round posts nothing for them, and names them again.
        rows = self.rows()
        code, out, err = self.cli("reviews")
        self.assertEqual((code, len(self.posts), self.rows()), (0, 1, rows))
        for name in ("TauCeti.Foo.one", "TauCeti.Foo.two", "TauCeti.Foo.three"):
            self.assertIn(name, out)

    def test_old_shaped_rows_are_dropped_with_why(self):
        self.old_audit({"TauCeti.Foo.one": "Correctly stated: `one` is 1.", "TauCeti.Foo.two": ""})
        code, out, err = self.cli("reviews")
        self.assertEqual(code, 0, err)
        self.assertEqual((self.posts, self.gh.bodies), ([], []))
        self.assertEqual([(r["file"], r["main"], r["state"], r.get("why")) for r in self.rows()],
                         [(FILE, self.c2, "dropped", "the site takes standard-review approvals now")])
        self.assertEqual(self.states(), {("dropped", "TauCeti.Foo.one"), ("dropped", "TauCeti.Foo.two")})
        # Dropped once: a later round leaves it.
        self.assertEqual(self.cli("reviews")[0], 0)
        self.assertEqual(len(self.rows()), 1)

    def test_an_entry_the_site_would_refuse_waits_for_re_review(self):
        # One recorded under laxer checks, or a line edited by hand: `post` refuses a whole comment for one such action,
        # so it waits for a re-review, and the rest of the file goes up.
        v_one, v_three = self.version("TauCeti.Foo.one"), self.version("TauCeti.Foo.three")
        self.append("audits", {"file": FILE, "matrix": MATRIX, "model": MODEL,
                               "yes": {"TauCeti.Foo.one": {"cells": {a: s for a, s in CELLS.items() if a != "junk"},
                                                           "approve": v_one},
                                       "TauCeti.Foo.two": {"cells": CELLS},
                                       "TauCeti.Foo.three": {"cells": CELLS, "approve": v_three}},
                               "blob": self.git("rev-parse", f"{self.c2}:{FILE}"), "main": self.c2,
                               "audited_at": "2026-10-31T10:00:00Z", "owner": OWNER, "decls": 4, "findings": []})
        code, out, err = self.cli("reviews")
        self.assertEqual(code, 0, err)
        [post] = self.posts
        self.assertEqual(post["actions"], [{"approve": "TauCeti.Foo.three", "version": v_three, "cells": CELLS}])
        self.assertEqual(self.states(), {("posted", "TauCeti.Foo.three"), ("re-review", "TauCeti.Foo.one"),
                                         ("re-review", "TauCeti.Foo.two")})
        self.assertIn("junk", out)

    def test_rows_written_before_settle_their_audits(self):
        # Under 0.81, a row of the reviews ledger settled the whole audit, and named no declarations.
        self.old_audit({"TauCeti.Foo.one": "Correctly stated."})
        self.append("reviews", {"file": FILE, "main": self.c2, "site": self.c2, "state": "posted", "yeses": 1,
                                "at": "2026-10-29T11:00:00Z", "owner": OWNER})
        code, out, err = self.cli("reviews")
        self.assertEqual((code, self.posts, len(self.rows())), (0, [], 1))

    def test_reviews_wait_until_the_site_shows_the_file(self):
        self.audit({"TauCeti.Foo.one": {"cells": CELLS, "approve": self.version("TauCeti.Foo.one")}})
        self.site.commit = self.c1  # behind the commit audited, which added the file
        code, out, err = self.cli("reviews")
        self.assertEqual((code, self.posts, self.rows()), (0, [], []))
        self.site.commit = self.c2
        self.assertEqual(self.cli("reviews")[0], 0)
        self.assertEqual((len(self.gh.bodies), self.states()), (1, {("posted", "TauCeti.Foo.one")}))

    def test_a_file_changed_before_the_site_showed_it_is_dropped(self):
        self.audit({"TauCeti.Foo.one": {"cells": CELLS, "approve": self.version("TauCeti.Foo.one")}})
        self.site.commit = self.c3  # past the commit audited, with the file changed
        code, out, err = self.cli("reviews")
        self.assertEqual((code, self.posts), (0, []))
        self.assertEqual(self.states(), {("dropped", "TauCeti.Foo.one")})

    def test_a_name_the_site_has_no_page_for_is_left_out(self):
        self.site.names.remove("TauCeti.Foo.four")
        del self.site.reviews["TauCeti.Foo.four"]
        self.audit({"TauCeti.Foo.one": {"cells": CELLS, "approve": self.version("TauCeti.Foo.one")},
                    "TauCeti.Foo.four": {"cells": CELLS, "write": TEXT_FOUR}})
        code, out, err = self.cli("reviews")
        self.assertEqual(code, 0, err)
        [post] = self.posts
        self.assertEqual([a.get("approve") or a.get("write") for a in post["actions"]], ["TauCeti.Foo.one"])
        self.assertIn("TauCeti.Foo.four", out)
        self.assertEqual(self.states(), {("posted", "TauCeti.Foo.one"), ("left out", "TauCeti.Foo.four")})

    def test_a_post_that_fails_is_tried_again_next_round(self):
        self.audit({"TauCeti.Foo.one": {"cells": CELLS, "approve": self.version("TauCeti.Foo.one")}})
        self.gh.fail = True
        code, out, err = self.cli("reviews")
        self.assertEqual((code, self.gh.bodies, self.rows()), (0, [], []))
        self.gh.fail = False
        self.assertEqual(self.cli("reviews")[0], 0)
        self.assertEqual((len(self.gh.bodies), self.states()), (1, {("posted", "TauCeti.Foo.one")}))


class ReReviewTests(Case):
    def test_yes_command_replaces_entries(self):
        self.audit({"TauCeti.Foo.one": {"cells": CELLS, "approve": STALE},
                    "TauCeti.Foo.three": {"cells": CELLS, "approve": STALE},
                    "TauCeti.Foo.four": {"cells": CELLS, "approve": STALE}})
        self.cli("reviews")
        self.assertEqual((self.posts, len(self.states())), ([], 3))  # all three wait for a re-review
        v_one, v_three = self.version("TauCeti.Foo.one"), self.version("TauCeti.Foo.three")
        code, out, err = self.cli("yes", self.json_file({"file": FILE, "yes": {
            "TauCeti.Foo.one": {"cells": CELLS, "approve": v_one},
            "TauCeti.Foo.three": {"cells": CELLS, "edit": v_three, "note": "says where the sum is taken",
                                  "text": EDIT_THREE}}}))
        self.assertEqual(code, 0, err)
        code, out, err = self.cli("reviews")
        self.assertEqual(code, 0, err)
        [post] = self.posts
        self.assertEqual(post["actions"], [
            {"approve": "TauCeti.Foo.one", "version": v_one, "cells": CELLS},
            {"edit": "TauCeti.Foo.three", "parent": v_three, "cells": CELLS, "note": "says where the sum is taken",
             "dropped": [], "text": EDIT_THREE}])
        self.assertEqual(self.states(), {("posted", "TauCeti.Foo.one"), ("posted", "TauCeti.Foo.three"),
                                         ("re-review", "TauCeti.Foo.one"), ("re-review", "TauCeti.Foo.three"),
                                         ("re-review", "TauCeti.Foo.four")})
        # Posted once; four still waits for its re-review.
        code, out, err = self.cli("reviews")
        self.assertEqual((code, len(self.posts)), (0, 1))
        self.assertIn("TauCeti.Foo.four", out)

    def test_yes_takes_only_declarations_waiting_for_a_re_review(self):
        self.audit({"TauCeti.Foo.one": {"cells": CELLS, "approve": STALE},
                    "TauCeti.Foo.three": {"cells": CELLS, "approve": self.version("TauCeti.Foo.three")}})

        def update(name):
            return self.json_file({"file": FILE, "yes": {name: {"cells": CELLS, "approve": self.version(name)}}})

        # Before `reviews` has looked, nothing waits for a re-review.
        code, out, err = self.cli("yes", update("TauCeti.Foo.one"))
        self.assertEqual(code, 1, err)
        self.assertIn("TauCeti.Foo.one", err)
        self.cli("reviews")  # one now waits for a re-review, and three is posted
        rows = self.rows()
        for name, why in (("TauCeti.Foo.three", "posted"),  # posted already
                          ("TauCeti.Foo.four", "TauCeti.Foo.four"),  # audited, with no review in the audit
                          ("TauCeti.Foo.five", "TauCeti.Foo.five")):  # not in the audit at all
            with self.subTest(name):
                code, out, err = self.cli("yes", self.json_file({"file": FILE, "yes": {
                    name: {"cells": CELLS, "approve": "dd83c85a488e22c8"}}}))
                self.assertEqual(code, 1, err)
                self.assertIn(why, err)
                self.assertEqual(self.rows(), rows)
        code, out, err = self.cli("yes", update("TauCeti.Foo.one"))
        self.assertEqual(code, 0, err)
        self.assertEqual(len(self.rows()), len(rows) + 1)

    def test_yes_command_refuses_what_it_could_not_post(self):
        self.audit({"TauCeti.Foo.one": {"cells": CELLS, "approve": STALE}})
        self.cli("reviews")  # it waits for a re-review
        before = self.rows()
        fine = {"cells": CELLS, "approve": self.version("TauCeti.Foo.one")}
        without_junk = {a: s for a, s in CELLS.items() if a != "junk"}
        for update, why in (
                ({"file": FILE, "yes": {"TauCeti.Foo.one": {"cells": without_junk, "approve": fine["approve"]}}},
                 "junk"),
                ({"file": FILE, "yes": {"TauCeti.Foo.one": {"cells": CELLS}}}, "TauCeti.Foo.one"),
                ({"file": FILE, "yes": {"TauCeti.Foo.five": fine}}, "TauCeti.Foo.five"),
                ({"file": "TauCeti/Other.lean", "yes": {"TauCeti.Other.zero": fine}}, "TauCeti/Other.lean"),
                ({"file": FILE, "yes": {}}, "yes"),
                ({"file": FILE, "yes": {"TauCeti.Foo.one": fine}, "model": "GPT-6 Astra"}, "model")):
            with self.subTest(why=why):
                code, out, err = self.cli("yes", self.json_file(update))
                self.assertEqual(code, 1, err)
                self.assertIn(why, err)
                self.assertEqual(self.rows(), before)


if __name__ == "__main__":
    unittest.main()
