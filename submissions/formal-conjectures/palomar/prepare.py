"""Export one Descartes theorem and its Lean source dependencies as a Lake project."""

import argparse
import json
import re
import shutil
import tempfile
from pathlib import Path
from string import Template


FACTOR = """(1 < w ∧ ¬ w.Prime) ∧ Odd (m * w) ∧ Nat.Coprime m w ∧
      ArithmeticFunction.sigma 1 m * (w + 1) = 2 * m * w"""

TOTH = "descartes_non_example_factor_gt_ten_pow_twelve"
CUBE = "descartes_cubeFree_lt_seven_primeFactors_unique"
MATHLIB = "Mathlib.NumberTheory.ArithmeticFunction.Misc"
REPO = Path(__file__).resolve().parents[3]
CUBE_DIR = Path(__file__).resolve().parents[1] / "cube-free"
IMPORT = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)\s*$")


def theorem_parts(target):
    if target == "toth":
        return (
            TOTH,
            f"""/-- Tóth's cofactor bound for a Descartes factorization. -/
theorem {TOTH} (m w : ℕ)
    (hf : {FACTOR})
    (hne : m * w ≠ 198585576189) : 10 ^ 12 < m""",
            "OddPerfect.TothTrillion",
            """by
  obtain ⟨⟨hw, hnp⟩, hodd, hcop, hbal⟩ := hf
  obtain ⟨hm, hwo⟩ := Nat.odd_mul.mp hodd
  exact OddPerfect.trillion_lt_spoof_cofactor
    ⟨hm, hwo, hw, hnp, hcop, by simpa only [Nat.mul_assoc] using hbal⟩ hne""",
        )
    return (
        CUBE,
        f"""/-- Banks, Güloğlu, Nevans and Saidak's uniqueness theorem for cube-free
Descartes integers with at most six distinct prime divisors. -/
theorem {CUBE} (n : ℕ)
    (hd : ∃ m w : ℕ, n = m * w ∧ {FACTOR})
    (hcf : ∀ ⦃x : ℕ⦄, x ^ 3 ∣ n → IsUnit x) (hcard : n.primeFactors.card < 7) :
    n = 198585576189""",
        "CubeFree",
        """by
  exact DescartesSubmission.catalog_cubeFree_lt_seven_primeFactors_unique n hd hcf hcard""",
    )


def module_source(imports, statement, proof):
    headers = "\n".join(f"public import {name}" for name in imports)
    return f"""module

{headers}

public section

namespace DescartesNumber

{statement} := {proof}

end DescartesNumber
"""


def proof_sources(entry):
    """Follow the one-module-per-import headers used in this Lean development."""
    sources = {}
    pending = [entry]
    while pending:
        name = pending.pop()
        if name in sources:
            continue
        relative = Path(*name.split(".")).with_suffix(".lean")
        source = (REPO if name.split(".")[0] == "OddPerfect" else CUBE_DIR) / relative
        content = source.read_text(encoding="utf-8")
        sources[name] = (source, relative)
        for line in content.splitlines():
            line = line.partition("--")[0].strip()
            if not re.match(r"^(?:(?:public|private|meta)\s+)*import\s", line):
                continue
            match = IMPORT.fullmatch(line)
            if not match:
                raise ValueError(f"{source}: unsupported import: {line}")
            module = match[1]
            if module.split(".")[0] not in {"Mathlib", "Lean", "Std", "Init"}:
                pending.append(module)
    return sources


def lake_config(manifest, names):
    mathlib, = (p for p in manifest["packages"] if p["name"] == "mathlib")
    config = f'''name = {json.dumps(manifest["name"])}
defaultTargets = ["Challenge", "Solution"]

[[require]]
name = "mathlib"
git = {json.dumps(mathlib["url"])}
rev = {json.dumps(mathlib["rev"])}

[[lean_lib]]
name = "OddPerfect"
globs = ["OddPerfect.+"]

[[lean_lib]]
name = "Challenge"

[[lean_lib]]
name = "Solution"
'''
    cube_modules = sorted(n for n in names if not n.startswith("OddPerfect."))
    if cube_modules:
        config += f'''
[[lean_lib]]
name = "CubeFreeProof"
roots = {json.dumps(cube_modules)}
'''
    return config


def metadata(target, theorem):
    if target == "toth":
        title = "Tóth's cofactor bound for Descartes factorizations"
        description = (
            "For an odd Descartes factorization m · w with composite spoof factor w, "
            "if m · w differs from 198585576189 then m exceeds one trillion."
        )
        paper = "On the Density of Spoof Odd Perfect Numbers"
        authors = ["L. Tóth"]
        doi = "10.12921/cmst.2021.0000005"
        relationship = "formalizes"
    else:
        title = "Cube-free Descartes integers with fewer than seven prime divisors"
        description = (
            "Every cube-free Descartes integer with fewer than seven distinct prime "
            "divisors equals 198585576189. The proof uses the prime support of its "
            "cofactor and divisibility relations for the sum of divisors."
        )
        paper = "Descartes numbers"
        authors = ["W. D. Banks", "A. M. Güloğlu", "C. W. Nevans", "F. Saidak"]
        doi = "10.1090/crmp/046/12"
        relationship = "independently-proves"
    template = Path(__file__).with_name("formalization.yaml.in").read_text(encoding="utf-8")
    return Template(template).substitute(
        title=title, description=description, paper=paper,
        authors=json.dumps(authors, ensure_ascii=False), doi=doi,
        relationship=relationship, theorem=f"DescartesNumber.{theorem}",
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", choices=["toth", "cube-free"])
    parser.add_argument("output", type=Path, help="a new directory with an existing parent")
    args = parser.parse_args()
    name, statement, implementation, proof = theorem_parts(args.target)
    config = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": [f"DescartesNumber.{name}"],
        "definition_names": [],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "enable_nanoda": True,
    }
    if args.output.exists():
        parser.error(f"output already exists: {args.output}")
    sources = proof_sources(implementation)
    manifest = json.loads((REPO / "lake-manifest.json").read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory(dir=args.output.parent) as temporary:
        export = Path(temporary) / "project"
        export.mkdir()
        for source, relative in sources.values():
            destination = export / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        for fixed in ["lean-toolchain", "lake-manifest.json"]:
            shutil.copy2(REPO / fixed, export / fixed)
        (export / "lakefile.toml").write_text(lake_config(manifest, sources), encoding="utf-8")
        (export / "Challenge.lean").write_text(
            module_source([MATHLIB], statement, "by sorry"), encoding="utf-8"
        )
        (export / "Solution.lean").write_text(
            module_source([MATHLIB, implementation], statement, proof), encoding="utf-8"
        )
        (export / "comparator.json").write_text(
            json.dumps(config, indent=2) + "\n", encoding="utf-8"
        )
        (export / "formalization.yaml.in").write_text(metadata(args.target, name), encoding="utf-8")
        export.rename(args.output)
    print(f"{args.target}: exported {len(sources)} proof modules to {args.output}")


if __name__ == "__main__":
    main()
