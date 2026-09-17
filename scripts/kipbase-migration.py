#!/usr/bin/env python3
"""Verify lossless KIP-base preservation, declaration coverage and inherited debt.

The source archive includes uncommitted changes to all tracked 4.28 files.
An optional local archive also preserves ignored history and local settings.
No files are extracted and no source is executed by this checker.
"""
import argparse
import collections
import difflib
import hashlib
import json
from pathlib import Path
import re
import tarfile

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = ROOT / "migration/kip-base"


def without_comments(text):
    """Blank nested Lean comments/strings, preserving offsets and line numbers."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i+2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                out[i:i+2] = "  "
                i += 2
            else:
                string = text[i] != '"'
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            out[i:end] = " " * (end-i)
            i = end
        elif text.startswith("/-", i):
            out[i:i+2] = "  "
            depth = 1
            i += 2
        elif text[i] == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            i += 1
    return "".join(out)


DECL = re.compile(
    r"(?m)^[ \t]*(?:(?:noncomputable|private|protected|unsafe|nonrec)\s+)*"
    r"(def|abbrev|theorem|lemma|axiom|structure|class|instance)\s+([^\s(:{\[]+)"
)


def inventory(text):
    clean = without_comments(text)
    declarations = list(DECL.finditer(clean))
    entries = [(m.group(1), m.group(2)) for m in declarations]
    debt = []
    for m in re.finditer(r"\b(axiom|sorry|admit)\b", clean):
        before = [d for d in declarations if d.start() <= m.start()]
        owner = before[-1].group(2) if before else "<unknown>"
        debt.append({"kind": m.group(), "declaration": owner,
                     "line": clean[:m.start()].count("\n") + 1})
    return entries, debt


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(audit_report=None, full_snapshot=False, write_port_diff=False):
    source = json.loads((ARCHIVE / "source-manifest.json").read_text())
    snapshot = [{"path": f["source"], "bytes": f["bytes"], "sha256": f["sha256"]}
                for f in source["files"]]
    with tarfile.open(ARCHIVE / "source-4.28.tar.gz", "r:gz") as tar:
        members = tar.getmembers()
        assert len(members) == len(snapshot), "archive file count changed"
        assert {m.name for m in members} == {f["path"] for f in snapshot}
        original = {}
        for entry in snapshot:
            member = tar.getmember(entry["path"])
            assert member.isfile(), f"unexpected archive type: {member.name}"
            data = tar.extractfile(member).read()
            assert len(data) == entry["bytes"] and digest(data) == entry["sha256"], member.name
            if member.name.endswith(".lean") and (
                member.name == "KIPBase.lean" or member.name.startswith("KIPBase/")
            ):
                original[member.name] = data.decode()
    counts = collections.Counter()
    ledger = {}
    port_diff = []
    for entry in source["files"]:
        path = entry["source"]
        data = (ROOT / entry["destination"]).read_bytes()
        if path not in original:
            assert digest(data) == entry["sha256"], f"original material changed: {path}"
            continue
        assert digest(original[path].encode()) == entry["sha256"], path
        old_decls, old_debt = inventory(original[path])
        new_decls, new_debt = inventory(data.decode())
        port_diff.extend(difflib.unified_diff(
            original[path].splitlines(keepends=True), data.decode().splitlines(keepends=True),
            fromfile="KIP-base-4.28/" + path, tofile="KIP126-4.32.2/" + path))
        missing = collections.Counter(old_decls) - collections.Counter(new_decls)
        assert not missing, f"lost declarations in {path}: {missing}"
        # Lines can move, but no inherited assumption may silently be added or renamed.
        key = lambda d: (d["kind"], d["declaration"])
        assert collections.Counter(map(key, new_debt)) == collections.Counter(map(key, old_debt)), (
            f"trust debt changed in {path}; review and document it explicitly"
        )
        ledger[path] = {"namedDeclarations": len(old_decls), "inherited": old_debt}
        counts.update(d["kind"] for d in old_debt)
    expected = json.loads((ARCHIVE / "trust-ledger.json").read_text())
    assert ledger == expected, "trust ledger differs from the immutable source snapshot"
    patch = "".join(port_diff)
    patch_path = ARCHIVE / "port.patch"
    if write_port_diff:
        patch_path.write_text(patch)
    else:
        assert patch_path.read_text() == patch, "port.patch is stale; regenerate with --write-port-diff"
    for path in (ROOT / "KIPBase").rglob("*.lean"):
        rel = str(path.relative_to(ROOT))
        if rel not in original:
            _, debt = inventory(path.read_text())
            assert not debt, f"new file contains an assumption: {rel}"
    if audit_report:
        report = json.loads(Path(audit_report).read_text())
        assert report["cleanCompatibility"], "compatibility bridge has historical axiom dependencies"
        assert report["declarations"], "empty compiled audit"
        assert len(report["axioms"]) == counts["axiom"], "compiled/source axiom counts differ"
    if full_snapshot:
        complete = json.loads((ARCHIVE / "local/snapshot-manifest.json").read_text())
        with tarfile.open(ARCHIVE / "local/working-tree-4.28.tar.gz", "r:gz") as tar:
            assert len(tar.getmembers()) == len(complete)
            assert {m.name for m in tar.getmembers()} == {f["path"] for f in complete}
            for entry in complete:
                member = tar.getmember(entry["path"])
                assert member.isfile(), member.name
                data = tar.extractfile(member).read()
                assert len(data) == entry["bytes"] and digest(data) == entry["sha256"], member.name
        print(f"Full local working-tree backup verified: {len(complete)} files")
    print(f"KIP-base preservation: {len(source['files'])} tracked files, "
          f"{len(original)} original Lean modules; "
          f"inherited trust debt: {dict(counts)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-report", help="JSON from scripts/KIPBaseAudit.lean")
    parser.add_argument("--full-snapshot", action="store_true",
                        help="also verify the local backup of ignored/private working files")
    parser.add_argument("--write-port-diff", action="store_true",
                        help="refresh the reviewable diff against the original Lean sources")
    args = parser.parse_args()
    verify(args.audit_report, args.full_snapshot, args.write_port_diff)
