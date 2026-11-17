"""Tests of what `review_site.py` does since the bulk run of 2026-11-17: it refuses to post the review of one's own work
(`mine` says what is), posts withdrawals (`withdraw`), refuses an edit that moves only links, warns of a long text, reads
the Checks a roadmap names by a Lean name or in prose, backs off when the site answers 429, fetches a run's snapshot in a
few requests (`snapshot`), and shows what changed under a text written for an earlier version (`standard --tauceti`).
The logins are invented: alice, bob and carol.

Run them from the root of the repository: python3 -m unittest discover -s tests
"""
import contextlib
import gzip
import io
import json
import os
import sys
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "scripts"))
import review_site  # noqa: E402
from test_review_site import (AGENT, COMMIT, AstraCase, Case, FetchTests, Gh, IntakeReadsPostTests, Site,  # noqa: E402
                              V, approve, edit, entry, review, write)


class AuthoredSite(Site):
    """The fake site, with the authors it records of its declarations (`authors`: name to logins), and one person's
    accounts (`same`); with ``authors`` None, a site that records none."""

    def __init__(self, authors=None, same=(), **kw):
        super().__init__(**kw)
        self.authors, self.same = authors, same

    def get(self, path):
        out = super().get(path)
        if self.authors is None:
            return out
        if path == "meta.json":
            return {**out, "authors": {"recorded": True, "samePerson": [list(g) for g in self.same]}}
        if path.startswith("m/"):
            people = sorted({a for logins in self.authors.values() for a in logins})
            return {**out, "people": people, "decls": [
                {**e, **({"au": [people.index(a) for a in self.authors[e["name"]]]} if e["name"] in self.authors else {})}
                for e in out["decls"]]}
        return out


class SignedIn(Gh):
    """`gh`, signed in as ``login``."""

    def __init__(self, login="bob"):
        super().__init__()
        self.login = login

    def __call__(self, *args, body=None):
        if args[:2] == ("api", "user"):
            return self.login
        return super().__call__(*args, body=body)


class OwnWorkTests(Case):
    def setUp(self):
        super().setUp()
        self.text = review()
        self.site = AuthoredSite({"Fixture.a": ["alice", "Carol"]}, same=[("alice", "alice-two")])
        self.site.add("Fixture.a", entry(self.text)).add("Fixture.b")
        self.gh = SignedIn("bob")

    def test_post_refuses_ones_own_work(self):
        for login in ("alice", "carol", "alice-two"):
            with self.subTest(login=login):
                code, out, err = self.post(approve("Fixture.a", V(self.text)), extra=("--login", login))
                self.assertEqual((code, out), (1, ""))
                self.assertIn("line 1 (Fixture.a): it is your own work", err)
        # bob, as gh is signed in, is no author: it goes up.
        code, out, err = self.post(approve("Fixture.a", V(self.text)), write("Fixture.b", review(says="b")))
        self.assertEqual(code, 0, err)
        self.assertNotIn("own work", err)

    def test_a_site_that_records_no_authors_is_said_to(self):
        self.site.authors = None
        code, out, err = self.post(approve("Fixture.a", V(self.text)), extra=("--login", "alice"))
        self.assertEqual(code, 0, err)
        self.assertIn("could not check that none of these is your own work", err)

    def test_mine(self):
        code, out, err = self.cli("mine", "Fixture.a", "Fixture.b", "Fixture.nowhere", "--login", "Alice")
        self.assertEqual(code, 1)
        self.assertEqual(out.splitlines(), ["MINE Fixture.a: alice, Carol", "NOT-MINE Fixture.b",
                                            "UNKNOWN Fixture.nowhere: the site records no authors for it (no page, or "
                                            "not one of Tau Ceti's own)"])
        self.assertEqual(self.cli("mine", "Fixture.b")[0], 0)  # as bob, whom gh is signed in as
        self.assertEqual(self.cli("mine", "Fixture.nowhere")[0], 2)
        self.site.authors = None
        code, out, err = self.cli("mine", "Fixture.a")
        self.assertEqual(code, 2)
        self.assertIn("cannot say", err)


class WithdrawTests(Case):
    def setUp(self):
        super().setUp()
        self.text = review()
        self.site.add("Fixture.a", entry(self.text))

    def test_a_withdrawal_in_a_batch(self):
        row = {"withdraw": "Fixture.a", "version": V(self.text)[:8], "note": "it was my own work"}
        code, out, err = self.post(row)
        self.assertEqual(code, 0, err)
        self.assertIn(f"\nWithdraw: Fixture.a — {V(self.text)[:8]} — it was my own work\n", out)
        bad = [({"withdraw": "Fixture.a", "version": "xyz", "note": "n"}, "8 to 16 hex digits"),
               ({"withdraw": "Fixture.a", "version": V(self.text), "note": " "}, "say why you withdraw it"),
               ({"withdraw": "Fixture.a", "version": V(self.text), "note": "ask @carol"}, "would notify"),
               ({"withdraw": "Fixture.a", "version": V(self.text), "note": "n", "cells": {}}, "not a field")]
        for row, why in bad:
            with self.subTest(why=why):
                code, out, err = self.post(row)
                self.assertEqual(code, 1)
                self.assertIn(why, err)
        # A withdrawal and a change of one declaration go in two runs.
        code, out, err = self.post(row := {"withdraw": "Fixture.a", "version": V(self.text), "note": "n"},
                                   edit("Fixture.a", V(self.text), self.text.replace("§1", "§2"), "the section"))
        self.assertEqual(code, 1)
        self.assertIn("a withdrawal counts", err)

    def test_the_withdraw_command(self):
        code, out, err = self.cli("withdraw", "Fixture.a", V(self.text), "--note", "filed by mistake", "--agent", AGENT,
                                  "--dry-run")
        self.assertEqual(code, 0, err)
        self.assertTrue(out.startswith("<!-- agent: tool=Voyager; model=claude-fable-5-1; session=7 -->\n"))
        self.assertIn(f"Withdraw: Fixture.a — {V(self.text)} — filed by mistake", out)
        code, out, err = self.cli("withdraw", "Fixture.a", V(self.text), "--note", "filed by mistake", "--dry-run")
        self.assertEqual(code, 0, err)
        self.assertNotIn("<!-- agent", out)  # as a person: a maintainer's own write
        code, out, err = self.cli("withdraw", "Fixture.a", V(self.text), "--note", "x")
        self.assertEqual(code, 0, err)
        (args, body), = self.gh.calls
        self.assertEqual(args[:2], ("issue", "comment"))


class TextRulesTests(Case):
    def setUp(self):
        super().setUp()
        self.text = review(refs=("- [Fixture documentation, §1](https://github.com/o/r/blob/0123abcd/docs.md#L3).",))
        self.site.add("Fixture.a", entry(self.text)).add("Fixture.a_one")

    def test_an_edit_that_moves_only_links_is_refused(self):
        moved = self.text.replace("0123abcd", "89abcdef").replace("#L3", "#L4")
        code, out, err = self.post(edit("Fixture.a", V(self.text), moved, "the link at the current commit"))
        self.assertEqual(code, 1)
        self.assertIn("approve the text instead", err)
        added = self.text.replace("#L3).", "#L3).\n- Roadmap: Fixture, Layer 1, which states it.")
        self.assertEqual(self.post(edit("Fixture.a", V(self.text), added, "adds the roadmap target"))[0], 0)

    def test_a_long_text_is_said_to_be_long(self):
        long = review(says=" ".join(["word"] * 420))
        code, out, err = self.post(write("Fixture.a_one", long))
        self.assertEqual(code, 0, err)
        self.assertIn(f"its text is {review_site.words(long)} words, over the 150 to 400", err)

    def test_checks_by_lean_name_and_in_prose(self):
        refs = ("- Fixture documentation, §1.", "- Check `Fixture.a_one` — passes: its value at 1",
                '- Check "Its value at 0 is 0" — missing: nothing states it')
        text = review(refs=refs)
        self.assertEqual(review_site.items(text).checks, ["Fixture.a_one", "Its value at 0 is 0"])
        self.assertEqual(self.post(write("Fixture.a_one", text))[0], 0)
        for bullet, why in (("- Check `Fixture.a_two` — passes: it does", "not a declaration that exists"),
                            ("- Check `Fixture.a_one` — missing", "is a declaration of the library"),
                            ('- Check "Its value at 0 is 0": its value', "says nothing of what was found")):
            with self.subTest(bullet=bullet):
                code, out, err = self.post(write("Fixture.a_one", review(refs=(bullet,))))
                self.assertEqual(code, 1)
                self.assertIn(why, err)


class BackoffTests(FetchTests):
    def test_a_429_waits_longer_and_as_long_as_asked(self):
        def limited(times, after=None):
            calls = []

            def urlopen(url, timeout):
                calls.append(url)
                if len(calls) <= times:
                    raise review_site.urllib.error.HTTPError(url, 429, "Too Many Requests",
                                                             {"Retry-After": after} if after else {}, None)
                return self.answer(b'{"ok": 1}')(url, timeout)
            return urlopen

        for after, waits in ((None, [30, 60]), ("90", [90, 90])):
            with self.subTest(after=after), mock.patch.object(review_site.time, "sleep") as sleep, \
                    mock.patch.object(review_site.urllib.request, "urlopen", limited(2, after)), \
                    contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(review_site.get("standard/1.json"), {"ok": 1})
                self.assertEqual([c.args[0] for c in sleep.call_args_list], waits)

    def test_a_comment_github_limits_is_posted_again(self):
        calls = []

        def gh(*args, body=None):
            calls.append(args)
            if len(calls) == 1:
                raise review_site.GhError("HTTP 403: You have exceeded a secondary rate limit")
            return "https://github.com/o/r/issues/1#issuecomment-9"

        with mock.patch.object(review_site, "gh", gh), mock.patch.object(review_site.time, "sleep") as sleep, \
                contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(review_site.comment_on("1", "text"), "https://github.com/o/r/issues/1#issuecomment-9")
        self.assertEqual((len(calls), [c.args[0] for c in sleep.call_args_list]), (2, [60]))


class SnapshotTests(Case):
    def test_a_snapshot_in_three_reads(self):
        rows = [{"decl": "Fixture.a", "version": "0123456789abcdef", "text": review(), "authors": ["alice"]}]
        export = gzip.compress("".join(json.dumps(r) + "\n" for r in rows).encode("utf-8"))
        meta = {"library": {"commit": COMMIT}, "shards": {}, "built": "2026-11-17T10:00:00Z",
                "exports": {"standard": "standard.jsonl.gz", "dataset": "https://example.org/dataset.tar.gz"},
                "roadmap": {"repo": "TauCetiProject/TauCetiRoadmap", "commit": "f" * 40}}
        manifest = {"packages": [{"name": "mathlib", "rev": "e" * 40}]}
        asked = []

        def fetch_bytes(url):
            asked.append(url)
            return export

        def fetch(url):
            asked.append(url)
            return json.dumps(manifest)

        out_dir = self.dir / "snap"
        with mock.patch.object(review_site, "fetch_bytes", fetch_bytes):
            self.site.get = lambda path: (asked.append(path), meta)[1]
            code, out, err = self.cli("snapshot", str(out_dir), fetch=fetch)
        self.assertEqual(code, 0, err)
        self.assertEqual(len(asked), 3)  # meta.json, the reviews, Tau Ceti's manifest: no shard
        self.assertEqual([json.loads(line) for line in (out_dir / "standard.jsonl").read_text().splitlines()], rows)
        info = json.loads((out_dir / "snapshot.json").read_text())
        self.assertEqual((info["tauceti"], info["mathlib"], info["roadmap"], info["reviews"]),
                         (COMMIT, "e" * 40, "f" * 40, 1))
        self.assertIn(f"git -C {out_dir}/TauCeti checkout {COMMIT}", out)
        self.assertIn(f"checkout {'e' * 40}", out)

    def test_a_site_without_the_file_is_not_crawled(self):
        code, out, err = self.cli("snapshot", str(self.dir / "snap"))
        self.assertEqual(code, 2)
        self.assertIn("never crawl its shards", err)


class StaleTests(AstraCase):
    """A text written for an earlier version of `Fixture.triple`, whose hypothesis `h` was dropped since."""

    OLD = "/-- Three times. -/\ndef Fixture.triple (n : ℕ) (h : 0 < n) : ℕ :=\n  3 * n\n"

    def test_what_changed_under_a_text(self):
        old = self.commit_files({"Fixture.lean": self.OLD})
        now = self.commit_files({"Fixture.lean": "/-- Three times. -/\ndef Fixture.triple (n : ℕ) : ℕ :=\n  3 * n\n",
                                 self.PATH: (self.repo / self.PATH).read_text()})
        self.site.commit, self.site.path = now, "Fixture.lean"
        self.site.info["Fixture.triple"]["line"] = [1, 3]
        stale = {**entry(self.t1, current=False), "checkedFor": {"commit": old, "module": "Fixture",
                                                                  "name": "Fixture.triple"}}
        self.site.reviews["Fixture.triple"] = stale
        code, out, err = self.cli("standard", "Fixture.triple")
        self.assertEqual(code, 0, err)
        self.assertIn(f"written for Tau Ceti at {old[:12]}, where it was Fixture.triple in Fixture", out)
        self.assertIn("`standard --tauceti CHECKOUT` shows both", out)
        code, out, err = self.cli("standard", "Fixture.triple", "--tauceti", str(self.repo))
        self.assertEqual(code, 0, err)
        self.assertIn("the statement changed since:", out)
        self.assertIn("-def Fixture.triple (n : ℕ) (h : 0 < n) : ℕ", out)
        self.assertIn("+def Fixture.triple (n : ℕ) : ℕ", out)

    def test_the_statement_of_a_declaration(self):
        lines = ["namespace Fixture", "/-- doc -/", "@[simp] theorem triple_pos {n : ℕ}", "    (h : 0 < n) :",
                 "    0 < triple n := by", "  omega", "theorem triple_pos' : True := trivial"]
        self.assertEqual(review_site.statement_in(lines, "Fixture.triple_pos"),
                         "@[simp] theorem triple_pos {n : ℕ}\n    (h : 0 < n) :\n    0 < triple n")
        self.assertIsNone(review_site.statement_in(lines, "Fixture.triple_neg"))


class IntakeReadsWithdrawTests(IntakeReadsPostTests):
    """The site's own parser reads a withdrawal `post` writes, and its checks agree with the copies here."""

    def test_the_parser_reads_a_withdrawal(self):
        text = review()
        self.site.add("Fixture.a", entry(text))
        code, out, err = self.post({"withdraw": "Fixture.a", "version": V(text)[:8], "note": "filed in error — twice"})
        self.assertEqual(code, 0, err)
        cmd, = self.si.commands(out)
        f = self.si.given(cmd, self.si.FORMS["Withdraw", True])
        self.assertEqual((cmd.keyword, f["decl"], f["note"]), ("Withdraw", "Fixture.a", "filed in error — twice"))
        self.assertEqual(self.si.named(f["version"], {V(text)}), {V(text)})

    def test_the_new_copies_agree_with_the_sites(self):
        std = self.standard
        texts = [review(refs=("- Check `Foo.bar` — missing", '- Check "First words", `Foo.baz` — passes: yes',
                              "- Check “Other words” — sorry", "- Check *t_1*, `x:1` — passes", "- Check the roadmap")),
                 review(refs=("- [A](https://github.com/o/r/blob/0123abcd/x.md#L3).",)),
                 review(says=" ".join(["w"] * 30) + " [link](https://example.org/a)")]
        for t in texts:
            with self.subTest(text=t[:60]):
                self.assertEqual([tuple(c) for c in review_site.checks_of(t)],
                                 [(c.kind, c.key, c.result, c.carrier) for c in std.checks_of(t)])
                self.assertEqual(review_site.words(t), std.words(t))
                self.assertEqual(review_site.unlinked(t), std.unlinked(t))
                for names in (set(), {"Foo.bar", "Foo.baz"}):
                    self.assertEqual(review_site.check_problems(t, names.__contains__),
                                     std.check_problems(t, names.__contains__))
        moved = texts[1].replace("0123abcd", "89abcdef")
        added = texts[1] + "- Roadmap: X, which states it.\n"
        for parent, child in ((texts[1], moved), (texts[1], added), (texts[0], texts[1])):
            self.assertEqual(review_site.scope(parent, child), std.scope(parent, child))
        self.assertEqual(review_site.WORDS, std.WORDS)
        self.assertEqual(review_site.COMMAND.pattern, self.si.COMMAND.pattern)


if __name__ == "__main__":
    unittest.main()
