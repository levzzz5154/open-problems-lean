#!/usr/bin/env bash
set -euo pipefail

echo "1. Checking source files for sorry / admit / axiom / native_decide / unsafe / implemented_by..."
python3 - <<'EOF'
import glob, re, sys

files = sorted(f for f in glob.glob("**/*.lean", recursive=True) if not f.startswith(".lake/"))
bad = []
# Strip block comments /- ... -/ and line comments -- ... before scanning
def strip_comments(s):
    out = []
    i, n, depth = 0, len(s), 0
    while i < n:
        if depth == 0 and s[i:i+2] == "--":
            j = s.find("\n", i)
            if j == -1: break
            out.append("\n")
            i = j + 1
        elif s[i:i+2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and s[i:i+2] == "-/":
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(s[i])
            i += 1
    return "".join(out)

patterns = [
    (r"\bsorry\b", "sorry"),
    (r"\badmit\b", "admit"),
    (r"^\s*(?:private\s+|protected\s+)?axiom\b", "axiom"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\bunsafe\b", "unsafe"),
    (r"implemented_by", "implemented_by"),
    (r"\bsorryAx\b", "sorryAx"),
]

for f in files:
    code = strip_comments(open(f, encoding="utf-8").read())
    for pat, label in patterns:
        if re.search(pat, code, re.M):
            bad.append((f, label))

if bad:
    print("FAIL: forbidden tokens found:", bad)
    sys.exit(1)
print(f"OK: scanned {len(files)} Lean source files (0 forbidden tokens).")
EOF

echo "2. Auditing axioms of all local theorems via Lean kernel..."
TMP_CHECK="$(mktemp --suffix=.lean)"
trap 'rm -f "$TMP_CHECK"' EXIT

python3 - "$TMP_CHECK" <<'EOF'
import glob, sys

out_path = sys.argv[1]
files = sorted(f for f in glob.glob("**/*.lean", recursive=True) if not f.startswith(".lake/"))
mods = [f[:-5].replace("/", ".") for f in files]

with open(out_path, "w", encoding="utf-8") as out:
    for m in mods:
        out.write(f"import {m}\n")
    out.write("""import Lean
open Lean

#eval show MetaM Unit from do
  let env ← getEnv
  let mut bad : Array (Name × List Name) := #[]
  let mut total := 0
  let modNames := env.header.moduleNames
  for i in [:modNames.size] do
    let m := modNames[i]!
    let ms := m.toString
    if ms.startsWith "Mathlib" || ms.startsWith "Init" || ms.startsWith "Std" || ms.startsWith "Lean" ||
       ms.startsWith "Batteries" || ms.startsWith "Qq" || ms.startsWith "Aesop" ||
       ms.startsWith "ProofWidgets" || ms.startsWith "ImportGraph" || ms.startsWith "Plausible" then
      continue
    let modData := env.header.moduleData[i]!
    for cname in modData.constNames do
      if let some (.thmInfo _) := env.find? cname then
        total := total + 1
        let (_, st) := (CollectAxioms.collect cname).run env {}
        let nonStd := st.axioms.toList.filter fun ax =>
          ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
        if !nonStd.isEmpty then
          bad := bad.push (cname, nonStd)
  IO.println s!"Checked {total} theorems across local modules."
  if !bad.isEmpty then
    IO.println s!"FAIL: {bad.size} theorem(s) depend on non-standard axioms:"
    for (n, axs) in bad do
      IO.println s!"  {n}: {axs}"
    throwError "Non-standard axioms detected"
  IO.println "OK: all theorems depend only on [propext, Classical.choice, Quot.sound]."
""")
EOF

lake env lean "$TMP_CHECK"
