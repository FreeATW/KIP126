#!/usr/bin/env python3
"""Pure regression tests for the KIP126 exact-head status projection."""

from __future__ import annotations

import json
import pathlib
import unittest

from . import labels, projection, scoreboard, sync


ROOT = pathlib.Path(__file__).resolve().parents[2]
CONFIG = projection.load_config(ROOT / "scripts" / "pr_status" / "config.json")
HEAD = "a" * 40
OLD = "b" * 40
RECOMMENDATION = "c" * 64


def status(context: str, state: str, *, head: str = HEAD, creator: str = "github-actions[bot]", description: str = "") -> dict:
    return {
        "id": len(context),
        "sha": head,
        "context": context,
        "state": state,
        "created_at": "2026-08-24T00:00:00Z",
        "creator": {"login": creator},
        "description": description,
    }


def scoreboard_comment(states: dict, *, head: str = HEAD, sha: str | None = None, association: str = "OWNER") -> dict:
    meta = {
        "kind": "scoreboard",
        "repo": "SII-MATH/KIP126",
        "pr": 17,
        "head_sha": head,
        "rubrics_sha": sha or CONFIG["review_rubrics_sha"],
        "states": states,
    }
    return {
        "body": f"{scoreboard.MARKER}\n## AI review — approved\n<!--tauceti-meta:v1 {json.dumps(meta)}-->",
        "author_association": association,
        "updated_at": "2026-08-24T00:00:00Z",
        "html_url": "https://example.test/scoreboard",
    }


def facts(profile: str = "lean", review: dict | None = None, **overrides) -> dict:
    contexts = list(CONFIG["mechanical_contexts"])
    if profile in {"blueprint", "reviewer-mixed-sync"}:
        contexts.append("blueprint")
    result = {
        "repository": "SII-MATH/KIP126",
        "number": 17,
        "state": "open",
        "merged": False,
        "draft": False,
        "head_sha": HEAD,
        "mergeable": True,
        "mergeable_state": "clean",
        "paths": ["KIP126/Core.lean"] if profile == "lean" else ["blueprint/src/content.tex"],
        "profile": profile,
        "statuses": [status(context, "success") for context in contexts],
        "comments": [review] if review else [],
        "sync": {
            "profile": profile,
            "authorization_valid": profile != "reviewer-mixed-sync",
            "ancestry_valid": profile != "reviewer-mixed-sync",
            "paths_valid": profile != "reviewer-mixed-sync",
            "reason": "mixed-sync:not-required",
        },
    }
    result.update(overrides)
    return result


class ScoreboardTests(unittest.TestCase):
    def test_exact_green_required_rubrics_approve(self) -> None:
        rubrics = set(CONFIG["review_rubrics"]["lean"])
        result = scoreboard.evaluate(
            [scoreboard_comment({rubric: "green" for rubric in rubrics})],
            "SII-MATH/KIP126", 17, HEAD, rubrics, CONFIG["review_rubrics_sha"], {"OWNER"},
        )
        self.assertEqual(result["state"], "green")

    def test_stale_untrusted_wrong_pin_and_missing_rubrics_fail_closed(self) -> None:
        rubrics = set(CONFIG["review_rubrics"]["lean"])
        cases = [
            (scoreboard_comment({rubric: "green" for rubric in rubrics}, head=OLD), "stale"),
            (scoreboard_comment({rubric: "green" for rubric in rubrics}, association="NONE"), "untrusted"),
            (scoreboard_comment({rubric: "green" for rubric in rubrics}, sha=OLD), "untrusted"),
            (scoreboard_comment({next(iter(rubrics)): "green"}), "running"),
        ]
        for comment, expected in cases:
            with self.subTest(expected=expected):
                result = scoreboard.evaluate(
                    [comment], "SII-MATH/KIP126", 17, HEAD, rubrics,
                    CONFIG["review_rubrics_sha"], {"OWNER"},
                )
                self.assertEqual(result["state"], expected)

    def test_any_adverse_or_error_state_blocks_green(self) -> None:
        rubrics = set(CONFIG["review_rubrics"]["lean"])
        states = {rubric: "green" for rubric in rubrics}
        states[next(iter(rubrics))] = "blocking_request"
        self.assertEqual(
            scoreboard.evaluate([scoreboard_comment(states)], "SII-MATH/KIP126", 17, HEAD, rubrics,
                                CONFIG["review_rubrics_sha"], {"OWNER"})["state"],
            "blocked",
        )


class ProjectionTests(unittest.TestCase):
    def green(self, profile: str = "lean") -> dict:
        states = {rubric: "green" for rubric in CONFIG["review_rubrics"][profile]}
        return scoreboard_comment(states)

    def test_profiles_are_classified_from_changed_paths(self) -> None:
        self.assertEqual(projection.classify_profile(["KIP126/A.lean"]), "lean")
        self.assertEqual(projection.classify_profile(["blueprint/src/content.tex"]), "blueprint")
        self.assertEqual(
            projection.classify_profile(["KIP126/A.lean", "blueprint/src/content.tex"]),
            "reviewer-mixed-sync",
        )

    def test_green_scoreboard_is_the_only_semantic_ready_signal(self) -> None:
        decision = projection.reduce_facts(facts(review=self.green()), CONFIG, 1_800_000_000)
        self.assertTrue(decision["merge_allowed"])
        self.assertEqual(decision["target_label"], "ready-to-merge")
        self.assertEqual(decision["review"]["scoreboard_state"], "green")

    def test_mechanical_failure_precedes_review(self) -> None:
        value = facts(review=self.green())
        value["statuses"] = [status("scope", "failure"), status("build", "success"), status("bump-guard", "success")]
        decision = projection.reduce_facts(value, CONFIG)
        self.assertEqual(decision["phase"], "awaiting-author")
        self.assertEqual(decision["reason"], "scope:failure")

    def test_warning_only_build_requires_human_merge(self) -> None:
        value = facts(review=self.green())
        value["statuses"] = [
            status("scope", "success"),
            status("build", "success"),
            status("bump-guard", "success"),
            status("warnings", "failure"),
        ]
        decision = projection.reduce_facts(value, CONFIG)
        self.assertFalse(decision["merge_allowed"])
        self.assertEqual(decision["phase"], "awaiting-author")
        self.assertEqual(decision["reason"], "warnings:failure")

    def test_absent_stale_blocked_and_running_scoreboards_have_distinct_phases(self) -> None:
        rubrics = CONFIG["review_rubrics"]["lean"]
        cases = [
            (None, "awaiting-review"),
            (scoreboard_comment({rubric: "green" for rubric in rubrics}, head=OLD), "awaiting-review"),
            (scoreboard_comment({**{rubric: "green" for rubric in rubrics}, rubrics[0]: "blocking_block"}), "awaiting-author"),
            (scoreboard_comment({**{rubric: "green" for rubric in rubrics}, rubrics[0]: "stale"}), "review-in-progress"),
        ]
        for comment, phase in cases:
            with self.subTest(phase=phase):
                self.assertEqual(projection.reduce_facts(facts(review=comment), CONFIG)["phase"], phase)

    def test_mixed_requires_blueprint_and_valid_sync_tuple(self) -> None:
        review = self.green("reviewer-mixed-sync")
        value = facts("reviewer-mixed-sync", review)
        value["sync"] = {
            "profile": "reviewer-mixed-sync",
            "authorization_valid": True,
            "ancestry_valid": True,
            "paths_valid": True,
            "reason": "mixed-sync:valid",
        }
        self.assertTrue(projection.reduce_facts(value, CONFIG)["merge_allowed"])
        value["sync"]["authorization_valid"] = False
        value["sync"]["reason"] = "mixed-sync:authorization-missing-or-mismatched"
        decision = projection.reduce_facts(value, CONFIG)
        self.assertFalse(decision["merge_allowed"])
        self.assertEqual(decision["phase"], "awaiting-author")


class SyncTests(unittest.TestCase):
    def commit(self, source: str = OLD, recommendation: str = RECOMMENDATION) -> dict:
        return {
            "commit": {"message": f"sync blueprint\n\nEuler-Blueprint-Sync-From: {source}\nEuler-Blueprint-Recommendation: {recommendation}\n"},
            "parents": [{"sha": source}],
        }

    def test_valid_exact_parent_authorization_and_blueprint_only_delta(self) -> None:
        authorization = status(
            CONFIG["sync_context"], "success", head=OLD, creator="surenny",
            description=f"recommendation={RECOMMENDATION}",
        )
        result = sync.validate(
            HEAD, "SII-MATH/KIP126", "SII-MATH/KIP126", self.commit(),
            ["blueprint/src/content.tex"], [authorization], CONFIG["sync_context"], {"surenny"},
        )
        self.assertTrue(result["authorization_valid"])
        self.assertTrue(result["ancestry_valid"])
        self.assertTrue(result["paths_valid"])

    def test_forged_trailer_fork_and_non_blueprint_delta_fail(self) -> None:
        result = sync.validate(
            HEAD, "fork/KIP126", "SII-MATH/KIP126", self.commit(),
            ["KIP126/A.lean"], [], CONFIG["sync_context"], {"surenny"},
        )
        self.assertFalse(result["authorization_valid"])
        self.assertFalse(result["paths_valid"])
        self.assertIn("mixed-sync:fork-not-writable", result["reasons"])


class LabelTests(unittest.TestCase):
    def test_changes_are_idempotent_and_preserve_unmanaged_labels(self) -> None:
        self.assertEqual(
            labels.desired_changes(["bug", "awaiting-CI", "awaiting-review"], "awaiting-review", CONFIG),
            {"remove": ["awaiting-CI"], "add": None},
        )
        self.assertEqual(
            labels.desired_changes(["bug", "awaiting-review"], "awaiting-review", CONFIG),
            {"remove": [], "add": None},
        )


if __name__ == "__main__":
    unittest.main()
