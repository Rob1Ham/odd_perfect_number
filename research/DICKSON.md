# Finiteness with a bounded number of prime factors

For every natural number k, the set of odd perfect numbers having at most k distinct prime factors is finite. The declaration `OddPerfect.dickson_finite` proves this statement directly using mathlib's `Nat.Perfect`. It gives a finite set for each k. Its bound grows with k, so an infinite sequence with increasing numbers of prime factors is still possible. [Dickson (1913)](https://doi.org/10.2307/2370405) · [Lean proof](../OddPerfect/Dickson.lean)

## A product proof

Write e for the exact exponent of a prime p. Its contribution to σ(N)/N splits into p/(p−1) and (x−1)/x, where x = p^(e+1). For each p, label the former factor by p and the latter by x. A cutoff t gives a partial product of the factors whose labels are at most t. All factors together multiply to two.

Suppose some labels remain above t. Let C be the primes for which both labels have been seen, and O the primes with only the first label seen. If O is nonempty, equating the partial product to two forces 4 into the product of the divisor sums of the completed components. Indeed, clearing denominators introduces 2 from the target and an even factor p−1 for any p in O. The numerator outside the completed divisor sums is odd. The completed divisor sums divide σ(N)=2N by multiplicativity, contradicting oddness. If O is empty, at least one complete component is missing. Each missing component has abundancy strictly greater than one, so the partial product is less than two. The proof covers the cutoff that has seen every base while a closing label is still missing. [Partial product lemma](../OddPerfect/PartialAbundancy.lean)

Now write the imbalance after clearing the processed factors as two different positive integers U,V. The unprocessed factors must correct their ratio. With m factors remaining, at least one remaining label is at most m·max(U,V). To see this, suppose every remaining label is at least D. Each remaining ratio, in either orientation, is at least 1−1/D. Bernoulli's inequality bounds their product from below by 1−m/D. For U<V this gives D(V−U) ≤ mV, and V−U is at least one. Swapping U and V handles the other orientation. This argument uses exact rational arithmetic. [Gap and iteration](../OddPerfect/ProductGap.lean)

With at most K=2k labels, processed products at cutoff t≥1 are bounded by 2tᴷ, including the initial factor of two. Replacing t by max(t,2Ktᴷ) therefore includes at least one additional label whenever one remains. After K rounds all labels have been included. Multiplying the resulting bound across at most k prime powers bounds N. This coarse recurrence is the one certified by `le_of_bounded_prime_count`. Nielsen published a substantially sharper explicit bound, N < 2^(4^k). Pollack's different proof uses compactness and his corrected continuity statement on spaces of uniformly bounded support cardinality. [Nielsen (2003)](https://mathdept.byu.edu/~pace/upper_bound_web.pdf) · [Pollack](https://www.pollack-math.net/dickson-AMM.pdf) · [Erratum](https://www.pollack-math.net/dickson-errata.pdf)

An independent argument with the primitive-divisor theorem covers a different input. If every prime divisor is at most B, then the full length e+1 of every component occurs as an order modulo another prime r≤B, so e+1<r. Consequently N divides (B!)ᴮ. The formal proof of Dickson's theorem above uses the adjacent-factor argument for both bases and exponents. [Bounded support](../OddPerfect/BoundedSupport.lean)

## Positive odd spoof factorizations

The same proof works for indexed odd bases greater than one and positive exponents whenever the product of their geometric sums is twice the represented integer. Two indices can carry identical pairs. The oddness argument uses divisibility into the full formal sum, which follows from its product formula. Bounding both coordinates of each pair gives finiteness of the set of ordered tuples of fixed length. If a base equals one, its abundancy is already at least two and every other positive component raises it strictly. The only balanced tuple containing such a base is the single entry (1,1). This proves the full positive case of Corollary 4.3. The signed result has additional hypotheses. [BYU Computational Number Theory Group, §4](https://mathdept.byu.edu/~pace/Spoof_web.pdf) · [Lean proofs](../OddPerfect/SpoofFiniteness.lean)

Run `lake build OddPerfect.Dickson OddPerfect.BoundedSupport OddPerfect.SpoofFiniteness` to reproduce the arguments. The project audit includes their named declarations through the public module.

## An explicit bound for the radical and size

Write k = ω(N) and R for the product of the distinct primes of an odd perfect N. The declaration `radical_squared_size_upper` gives

$$4k R^2 N \le (4k)^{4^k}.$$

This bound follows from the same elementary product-gap argument that proves finiteness. For each true prime p use the two labels p and p^(vₚ(N)+1). Their product over all 2k labels is R²N. The argument also gives a bound for every positive odd spoof list with all bases greater than one and positive exponents. In that setting R is replaced by the product of the indexed bases, with repetitions preserved. Nielsen's published upper bound N < 2^(4^k) remains a stronger absolute bound. [True-prime specialization](../OddPerfect/RadicalUpperBound.lean) · [Spoof product bound](../OddPerfect/SpoofFiniteness.lean) · [Nielsen, Theorem 1](https://mathdept.byu.edu/~pace/upper_bound_web.pdf)

For any threshold t, let A be the product of all labels at most t, let m count the remaining labels, and take C=4k. The checked prefix bound is C times the entire product at most (CA)^(2^m). A new cutoff is an actual remaining label at most CA. If g labels enter together, their product is at most (CA)^g. The new scaled prefix is therefore at most (CA)^(g+1), and g+1 ≤ 2^g. This accounts for equal labels across different entries. [Product bound from an arbitrary cutoff](../OddPerfect/LabelProductBound.lean)
