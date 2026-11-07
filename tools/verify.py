#!/usr/bin/env python3
"""Offline acceptance lane. Tests the Lean oracle; does not model the application."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
LAKE = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
ORACLE = ROOT / ".lake/build/bin/oracle"
REPORT = ROOT / "reports/latest.json"
ALLOW_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(args, *, input=None, timeout=180):
    result = subprocess.run(args, cwd=ROOT, input=input, capture_output=True,
                            text=True, timeout=timeout)
    if result.returncode:
        raise AssertionError(f"command failed ({result.returncode}): {args}\n"
                             f"{result.stdout}\n{result.stderr}")
    return result.stdout + (result.stderr if args[0] != str(ORACLE) else "")


def oracle(value=None, *, raw=None, args=()):
    output = run([str(ORACLE), *args], input=raw if raw is not None else json.dumps(value))
    return json.loads(output)


def contains(actual, expected, at="result"):
    if isinstance(expected, dict):
        assert isinstance(actual, dict), (at, actual, expected)
        for key, value in expected.items():
            assert key in actual, (at, key, actual)
            contains(actual[key], value, f"{at}.{key}")
    elif isinstance(expected, list):
        assert isinstance(actual, list) and len(actual) == len(expected), (at, actual, expected)
        for index, (a, e) in enumerate(zip(actual, expected)):
            contains(a, e, f"{at}[{index}]")
    else:
        assert type(actual) is type(expected) and actual == expected, (at, actual, expected)


def source_digest():
    paths = sorted([*ROOT.glob("*.lean"), *ROOT.glob("Lantern/*.lean"),
                    *ROOT.glob("tools/*.py"), *ROOT.glob("fixtures/*.json"),
                    ROOT / "lean-toolchain", ROOT / "lakefile.toml",
                    ROOT / "lake-manifest.json"])
    digest = hashlib.sha256()
    for path in paths:
        digest.update(str(path.relative_to(ROOT)).encode() + b"\0" + path.read_bytes() + b"\0")
    return digest.hexdigest()


def verify():
    report = {
        "status": "running", "startedUtc": datetime.now(timezone.utc).isoformat(),
        "sourceSha256": source_digest(), "lane": "local Lean design oracle",
        "claims": {}, "applicationConformance": {
            "status": "NOT_RUN", "reason": "No live Python runner/collector exists in this repository."},
        "assumptions": ["trusted serialized coordinator and recorder", "faithful run/key/payload identity",
                        "instrumented calls only", "simulated central ledger only"],
        "notEstablished": ["external truth", "hidden tool coverage", "causal influence or fairness",
                           "external exactly-once execution", "application refinement", "hackathon eligibility"],
    }
    REPORT.parent.mkdir(exist_ok=True)
    REPORT.write_text(json.dumps(report, indent=2) + "\n")
    start = time.monotonic()
    try:
        run([LAKE, "build"], timeout=300)
        report["build"] = "PASS"
        report["leanVersion"] = run([LAKE, "env", "lean", "--version"]).strip()
        core = [p for p in [*ROOT.glob("*.lean"), *ROOT.glob("Lantern/*.lean")]
                if p.name != "Audit.lean"]
        for path in core:
            # A source policy check supplements, never replaces, the transitive axiom audit.
            assert not re.search(r"\b(sorry|admit|axiom|native_decide|implemented_by)\b", path.read_text()), path
        audit = run([LAKE, "env", "lean", "Lantern/Audit.lean"])
        (ROOT / "reports/axioms.txt").write_text(audit)
        parsed = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
        audited = {}
        for name, axioms in parsed:
            used = set(filter(None, (a.strip() for a in axioms.split(","))))
            assert used <= ALLOW_AXIOMS, (name, used - ALLOW_AXIOMS)
            audited[name] = sorted(used)
        for name in re.findall(r"'([^']+)' does not depend on any axioms", audit):
            audited[name] = []
        exported = {"Lantern." + name for p in core for name in re.findall(
            r"^theorem\s+(\w+)", p.read_text(), flags=re.M)}
        assert set(audited) == exported and len(audited) >= 15, (set(audited), exported)
        report["axioms"] = {"status": "PASS", "theorems": audited,
                            "allowedStandardFoundations": sorted(ALLOW_AXIOMS)}
        run([LAKE, "env", "leanchecker", "--fresh", "Lantern.Wire"], timeout=600)
        report["storedProofReplay"] = {
            "status": "PASS", "command": "lake env leanchecker --fresh Lantern.Wire",
            "scope": "module and imported declarations replayed through the Lean kernel; not an independent checker"}
        run([LAKE, "env", "lean", "Lantern/Examples.lean"])
        report["kernelCheckedExamples"] = "PASS"
        usage = subprocess.run([str(ORACLE), "--invalid"], cwd=ROOT,
                               capture_output=True, text=True, timeout=10)
        assert usage.returncode == 2 and not usage.stdout and "usage:" in usage.stderr
        fixtures = json.loads((ROOT / "fixtures/traces.json").read_text())
        results = {}
        for fixture in fixtures:
            actual = oracle(fixture.get("input"), raw=fixture.get("raw"))
            contains(actual, fixture["expect"], fixture["name"])
            results[fixture["name"]] = actual
        assert any(r["accepted"] for r in results.values())
        assert any(not r["accepted"] for r in results.values())
        # Check the whole state, not merely the number of ledger entries.
        duplicate = next(f for f in fixtures if f["name"] == "exact_retry_is_idempotent")
        once = oracle({"events": duplicate["input"]["events"][:-1]})
        assert once == results[duplicate["name"]]
        sealed = next(f for f in fixtures if f["name"] == "retry_after_seal_is_cached")
        assert oracle({"events": sealed["input"]["events"][:-1]}) == results[sealed["name"]]
        report["fixtures"] = {"status": "PASS", "count": len(fixtures),
                              "accepted": sum(r["accepted"] for r in results.values()),
                              "names": list(results), "fullStateIdempotence": "PASS"}
        mutants = oracle(args=["--mutants"])
        assert len(mutants) == 3
        for mutant, expected_length in zip(mutants, (1, 2, 4)):
            witness = mutant["violation"]
            assert witness is not None and len(witness) == expected_length, mutant
            assert not mutant["truncated"], mutant
            baseline = oracle({"events": witness})
            if expected_length == 4:
                # A repeated request is legal; its extra ledger effect is the bug.
                assert baseline["accepted"] and len(baseline["state"]["commitments"]) == 1
                assert len(mutant["violationState"]["commitments"]) == 2
            else:
                assert not baseline["accepted"], mutant
        report["mutants"] = {"status": "PASS", "searches": mutants,
                             "shortestWithin": "width-one alphabet; breadth-first search"}
        exploration = oracle(args=["--explore"])
        assert exploration["violation"] is None, exploration
        assert exploration["width"] == 2 and exploration["depthBound"] == 6
        assert exploration["states"] <= 50000 and exploration["edges"] > 0
        assert exploration["acceptedEdges"] + exploration["rejectedEdges"] == exploration["edges"]
        assert sum(exploration["statesByDepth"]) == exploration["states"]
        assert exploration["expandedStates"] <= exploration["poppedStates"] <= exploration["states"]
        report["exploration"] = {"status": "PASS", **exploration}
        for claim, theorem in {
            "supportedEvidence": "observed_references_supported",
            "honestCoverage": "complete_receipts_have_outcomes",
            "retrySafety": "commitment_keys_nodup",
        }.items():
            report["claims"][claim] = {"formalStatus": "PROVED_IN_MODEL",
                                       "theorem": "Lantern." + theorem,
                                       "runtimeEvidence": "fixtures and compiled Lean oracle only"}
        assert source_digest() == report["sourceSha256"], "sources changed during verification"
        report["status"] = "PASS"
    except Exception as error:
        report["status"] = "FAIL"
        report["failure"] = str(error)
        raise
    finally:
        report["elapsedSeconds"] = round(time.monotonic() - start, 3)
        report["finishedUtc"] = datetime.now(timezone.utc).isoformat()
        REPORT.write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(audited)} audited theorems; {len(fixtures)} fixtures; 3 detected mutants")
    print(f"Exploration: {exploration['states']} states, {exploration['edges']} edges, "
          f"truncated={exploration['truncated']}")
    print("Application conformance: NOT_RUN")
    print(REPORT)


if __name__ == "__main__":
    verify()
