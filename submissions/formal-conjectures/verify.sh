#!/usr/bin/env bash
# Run from anywhere in this checkout. Write intermediate modules to a temporary directory.
set -euo pipefail
packet=$(cd "$(dirname "$0")" && pwd)
cd "$packet/../.."
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
if [[ ${1-} != --cached ]]; then
  lake build OddPerfect.TothTrillion OddPerfect.ChenLuo OddPerfect.DeficientFourClassification \
    OddPerfect.ChainAbundancy OddPerfect.Spoof OddPerfect.DeficientThirdSource \
    OddPerfect.ParityDichotomy OddPerfect.SixthPowerBounds OddPerfect.QuasiperfectSupport OddPerfect.HarmonicFinite
fi
lake env bash -euo pipefail -c '
  packet=$1
  build=$2
  export LEAN_PATH="$build:${LEAN_PATH-}"
  for module in FactorChains Structure ThreeDivides Valuations CubeFree; do
    lean -j1 -R "$packet/cube-free" -o "$build/$module.olean" "$packet/cube-free/$module.lean"
  done
  lean -j1 "$packet/toth/Check.lean"
  lean -j1 "$packet/mathoverflow-310919/Check.lean"
  lean -j1 "$packet/partial/Consequences.lean"
  lean -j1 "$packet/partial/DescartesConsequences.lean"
' _ "$packet" "$build" | tee "$build/check.log"
python3 - "$build/check.log" <<'PY'
import re
import sys
from pathlib import Path
log = Path(sys.argv[1]).read_text()
allowed = {"propext", "Classical.choice", "Quot.sound"}
printed = set()
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    unexpected = {ax.strip() for ax in axioms.split(",") if ax.strip()} - allowed
    if unexpected:
        raise SystemExit(f"{name} depends on {sorted(unexpected)}")
    printed.add(name)
required = {
    "DescartesSubmission.cube_free_unique_of_spoof",
    "DescartesSubmission.catalog_cubeFree_lt_seven_primeFactors_unique",
    "DescartesSubmission.toth_cofactor_bound",
    "DescartesSubmission.second_descartes_restrictions",
    "OddPerfect.trillion_lt_spoof_cofactor",
    "OddPerfect.chen_luo_congruences",
    "OddPerfect.sigma_square_mod_eight_of_euler",
    *("OddPerfect.CatalogCases." + name for name in (
        "odd_almostPerfect_witness", "five_thirds_residue_primes", "ochem_rao_of_sixth_power_free",
        "quasiperfect_witness", "ore_no_prime_power", "ore_odd_of_at_most_two_primes")),
}
printed.update(re.findall(r"'([^']+)' does not depend on any axioms", log))
if missing := required - printed:
    raise SystemExit(f"Missing axiom reports for {sorted(missing)}")
print(f"Checked the axiom lists for all {len(required)} expected theorem declarations.")
PY
