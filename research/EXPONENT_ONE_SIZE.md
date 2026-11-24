# The Euler index at exponent one

Suppose an odd perfect number has Euler form $N=q m^2$, and write $i=\sigma(m^2)/q$. The checked inequalities are $q<2i$, $m^2\le i^2$, and $N<2i^3$. Together with the project's absolute certificate $10^{160}<N$, they give $10^{53}<i$. This specialization uses Euler exponent one. [Cubic inequality](../OddPerfect/ExponentOneSize.lean) · [160-digit specialization](../OddPerfect/ExponentOneSize160.lean)

Acquaah and Konyagin give $q^3<3N$, hence $q^2<3m^2$. The component identity gives $(q+1)i=2m^2$. Since $q\ge3$, these imply $2q^2<3(q+1)i\le4qi$, so $q<2i$. Since $q$ and $i$ are integral, $q+1\le2i$ and $2m^2\le2i^2$. Multiplying the two estimates bounds $N$. Every step, including the prime-size estimate and the absolute size specializations, is a Lean theorem in this repository. [Acquaah–Konyagin proof](../OddPerfect/AcquaahKonyagin.lean) · [Absolute size certificate](../OddPerfect/SizeBound160.lean)
