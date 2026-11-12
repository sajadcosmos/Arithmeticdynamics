# Statement map: results of the paper and their Lean statements

This file lists, for every numbered result of the paper *Arithmetic dynamics on unitary Cayley and
GCD graphs*, the Lean theorems that prove it, with their exact statements (doc-comment and
signature, copied verbatim from the source; proofs omitted). Section A gives the definitions that
model the objects of the paper, so that each formal statement can be compared with the
mathematics. It was generated from the source of release v1.1 and can be regenerated with
`python3 tools/statements.py`.

Conventions. `ZMod n` is ℤ/n. Vectors on the vertex set are functions `ZMod n → ℝ` (or `ℂ`).
The theorems use `variable {n : ℕ} [NeZero n]`, i.e. n ≥ 1; a hypothesis `1 < n` or `2 ≤ n` is
added where the paper assumes n ≥ 2. Connectivity of `Cay(ℤ/n, S)` is the hypothesis
`AddSubgroup.closure (S : Set (ZMod n)) = ⊤` (S generates ℤ/n); `lam2_pos_iff` proves it is
equivalent to λ₂ > 0, and `gcd_connected_iff` proves that for gcd graphs it is equivalent to
gcd(D) = 1. Quotients are sometimes stated multiplied out (`x * v = u` for `x = u / v`).
Norm estimates are stated for squared norms, `‖e(t)‖² ≤ (ρ²)^t ‖e(0)‖²`, which is equivalent to
`‖e(t)‖ ≤ ρ^t ‖e(0)‖`. Theorems marked (H1)–(H3) take the corresponding classical theorem as an
explicit hypothesis (Section B).

Build and check:

```bash
lake exe cache get
lake build
lake env lean AxiomCheck.lean     # every theorem: [propext, Classical.choice, Quot.sound] or fewer
```

## A. Definitions modelling the paper

### `unitaryCayley` — The unitary Cayley graph X_n as a Mathlib SimpleGraph on ZMod n: a ~ b iff a - b is a unit (Section 2.2).

`ArithmeticDynamics/Spectrum.lean`, line 17

```lean
/-- The unitary Cayley graph `X_n`: `a ∼ b` iff `a ≠ b` and `b - a` is a unit of `ℤ/n`. -/
def unitaryCayley : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (fun a b => IsUnit (b - a))
```

### `adj` — Adjacency operator of X_n: (Af)(i) = Σ_{u unit} f(i+u).

`ArithmeticDynamics/Spectrum.lean`, line 36

```lean
/-- The adjacency operator of `X_n` acting on functions `ℤ/n → ℂ`. -/
noncomputable def adj (f : ZMod n → ℂ) (i : ZMod n) : ℂ := ∑ u : (ZMod n)ˣ, f (i + u)
```

### `lap` — Laplacian of X_n on complex vectors: L = φ(n) I - A.

`ArithmeticDynamics/Spectrum.lean`, line 39

```lean
/-- The Laplacian operator `L = φ(n) I - A` of `X_n`. -/
noncomputable def lap (f : ZMod n → ℂ) (i : ZMod n) : ℂ :=
  (Nat.totient n : ℂ) * f i - adj n f i
```

### `lapR` — The same Laplacian on real vectors.

`ArithmeticDynamics/Fourier.lean`, line 79

```lean
/-- The Laplacian of `X_n` on real vectors. -/
noncomputable def lapR (f : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  (Nat.totient n : ℝ) * f i - ∑ u : (ZMod n)ˣ, f (i + u)
```

### `ramanujan` — Ramanujan sum c_n(j) = Σ_{u unit} e(uj/n).

`ArithmeticDynamics/Ramanujan.lean`, line 132

```lean
/-- The Ramanujan sum `c_n(j) = ∑_{u ∈ (ℤ/n)ˣ} e(j u / n)`: the adjacency eigenvalue of the
unitary Cayley graph `X_n` attached to the character `χ_j`. -/
noncomputable def ramanujan (n : ℕ) [NeZero n] (j : ZMod n) : ℂ :=
  ∑ u : (ZMod n)ˣ, ZMod.stdAddChar (j * (u : ZMod n))
```

### `r` — r(M) = μ(M)/φ(M), equation (2.1).

`ArithmeticDynamics/Extremal.lean`, line 14

```lean
/-- `r M = μ(M) / φ(M)`; the adjacency eigenvalues of `X_n` are `φ(n) · r(M)`. -/
noncomputable def r (M : ℕ) : ℝ := (moebius M : ℝ) / (Nat.totient M : ℝ)
```

### `lapEig` — Laplacian eigenvalue λ(k) = φ(n)(1 - r(ord k)), equation (2.4).

`ArithmeticDynamics/Spectrum.lean`, line 80

```lean
/-- The Laplacian eigenvalue of `X_n` attached to `χ_k`:  `λ(k) = φ(n) (1 - r(ord k))`. -/
noncomputable def lapEig (k : ZMod n) : ℝ := (Nat.totient n : ℝ) * (1 - r (addOrderOf k))
```

### `IsSymm` — Symmetric connection set S = -S.

`ArithmeticDynamics/Circulant.lean`, line 16

```lean
/-- A symmetric connection set: `S = -S`. -/
def IsSymm (S : Finset (ZMod n)) : Prop := ∀ s ∈ S, -s ∈ S
```

### `cLap` — Laplacian of a general circulant Cay(Z_n, S).

`ArithmeticDynamics/Circulant.lean`, line 31

```lean
/-- The Laplacian of `Cay(ℤ/n, S)` on real vectors. -/
noncomputable def cLap (f : ZMod n → ℝ) (i : ZMod n) : ℝ := (#S : ℝ) * f i - ∑ s ∈ S, f (i + s)
```

### `cSym` — Fourier symbol C_S(k), equation (2.2).

`ArithmeticDynamics/Circulant.lean`, line 41

```lean
/-- The (real) Fourier symbol `C_S(j) = ∑_{s∈S} cos(2π j s/n)`. -/
noncomputable def cSym (j : ZMod n) : ℝ := ∑ s ∈ S, cWeight j s
```

### `gcdSet` — Connection set S_D = {s : gcd(s,n) ∈ D} of the gcd graph X_n(D).

`ArithmeticDynamics/GcdGraph.lean`, line 17

```lean
/-- The connection set `S_D = {s : gcd(s, n) ∈ D}` of the gcd graph `X_n(D)`. -/
def gcdSet (n : ℕ) [NeZero n] (D : Finset ℕ) : Finset (ZMod n) :=
  univ.filter (fun s : ZMod n => Nat.gcd s.val n ∈ D)
```

### `ProperDivisors` — D consists of proper divisors of n (Section 2.3: n ∉ D).

`ArithmeticDynamics/GcdConsensus.lean`, line 356

```lean
/-- `D` is a set of proper divisors of `n`. -/
def ProperDivisors (n : ℕ) (D : Finset ℕ) : Prop := ∀ d ∈ D, d ∣ n ∧ d < n
```

### `lam2` — λ₂ of a circulant = min over k ≠ 0 of |S| - C_S(k).

`ArithmeticDynamics/GcdGraph.lean`, line 99

```lean
/-- The algebraic connectivity `λ₂ = min_{k ≠ 0} (|S| - C(k))` of a circulant, for `n ≥ 2`. -/
noncomputable def lam2 (S : Finset (ZMod n)) (hn : 1 < n) : ℝ :=
  (univ.erase (0 : ZMod n)).inf'
    ⟨1, mem_erase.mpr ⟨by haveI : Fact (1 < n) := ⟨hn⟩; exact one_ne_zero, mem_univ _⟩⟩
    (fun k => (#S : ℝ) - cSym S k)
```

### `avg` — Average of a vector.

`ArithmeticDynamics/ConsensusDynamics.lean`, line 18

```lean
/-- The average `x̄ = (1/n) ∑ x_j`. -/
noncomputable def avg (x : ZMod n → ℝ) : ℝ := (∑ j, x j) / n
```

### `err` — Consensus error x - x̄1.

`ArithmeticDynamics/ConsensusDynamics.lean`, line 21

```lean
/-- The consensus error `x - x̄ 1`. -/
noncomputable def err (x : ZMod n → ℝ) : ZMod n → ℝ := fun j => x j - avg x
```

### `sqNorm` — Squared Euclidean norm.

`ArithmeticDynamics/Fourier.lean`, line 89

```lean
/-- The squared Euclidean norm `∑ f_j²`. -/
noncomputable def sqNorm (f : ZMod n → ℝ) : ℝ := ∑ j : ZMod n, f j ^ 2
```

### `step` — One step x ↦ (I - εL)x of the consensus iteration on X_n (equation (4.1)).

`ArithmeticDynamics/ConsensusDynamics.lean`, line 24

```lean
/-- One step of the consensus iteration `x ↦ (I - ε L) x` on `X_n`. -/
noncomputable def step (ε : ℝ) (x : ZMod n → ℝ) : ZMod n → ℝ := fun j => x j - ε * lapR x j
```

### `cStep` — One step x ↦ (I - εL_S)x of the consensus iteration on a circulant.

`ArithmeticDynamics/GcdConsensus.lean`, line 29

```lean
/-- One step of the consensus iteration `x ↦ (I - ε L_S) x` on `Cay(ℤ/n, S)`. -/
noncomputable def cStep (S : Finset (ZMod n)) (ε : ℝ) (x : ZMod n → ℝ) : ZMod n → ℝ :=
  fun j => x j - ε * cLap S x j
```

### `DivSet` — The set {r(M) : M | n, M > 1} of normalised non-trivial adjacency eigenvalues.

`ArithmeticDynamics/Rates.lean`, line 32

```lean
/-- The values of `r` on the divisors `M > 1` of `n`.  By Hölder's formula these are the
normalised non-trivial adjacency eigenvalues of the unitary Cayley graph `X_n`. -/
def DivSet (n : ℕ) : Set ℝ := {x | ∃ M : ℕ, M ∣ n ∧ 1 < M ∧ r M = x}
```

### `rateOf` — (rmax - rmin)/(2 - rmax - rmin) = (λmax - λ₂)/(λmax + λ₂).

`ArithmeticDynamics/Rates.lean`, line 112

```lean
/-- `(λ_max - λ₂)/(λ_max + λ₂)` expressed through the extreme values `rmax`, `rmin` of `r`,
using `λ = φ(n) (1 - r)`. -/
noncomputable def rateOf (rmax rmin : ℝ) : ℝ := (rmax - rmin) / (2 - rmax - rmin)
```

### `IsRate` — ρ is the optimal rate ρ*(X_n) (Definition 4.2).

`ArithmeticDynamics/Rates.lean`, line 160

```lean
/-- `ρ*(X_n)` as a relation: `ρ` is the rate determined by the greatest and least
elements of `DivSet n`. -/
def IsRate (n : ℕ) (ρ : ℝ) : Prop :=
  ∃ rmax rmin : ℝ, IsGreatest (DivSet n) rmax ∧ IsLeast (DivSet n) rmin ∧ ρ = rateOf rmax rmin
```

### `rhoStar` — ρ*(X_m) as a function of m (0 for m < 2), used for the mean value.

`ArithmeticDynamics/MeanValue.lean`, line 17

```lean
/-- The optimal consensus rate `ρ*(X_m)` as a function of `m` (`0` for `m < 2`). -/
noncomputable def rhoStar (m : ℕ) : ℝ :=
  if h : 2 ≤ m then Classical.choose (exists_isRate h) else 0
```

### `meanRate` — The mean value of ρ* (series of Proposition 4.9).

`ArithmeticDynamics/MeanValue.lean`, line 561

```lean
/-- The mean value `ρ̄ = ∑_{p<q} (1/(pq)) ∏_{ℓ<q, ℓ≠p} (1 - 1/ℓ) · q/(2(p-1)(q-1)+q-2)`. -/
noncomputable def meanRate : ℝ := ∑' pq, pairWeight pq
```

### `kuramotoField` — Kuramoto vector field (5.1) on X_n with ω = 0.

`ArithmeticDynamics/Twisted.lean`, line 40

```lean
/-- The Kuramoto vector field on `X_n` (in the co-rotating frame):
`F(θ)_i = (K/φ(n)) ∑_u sin(θ_{i+u} - θ_i)`. -/
noncomputable def kuramotoField (K : ℝ) (θ : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  K / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, sin (θ (i + u) - θ i)
```

### `cField` — Kuramoto vector field (5.1) on a general circulant.

`ArithmeticDynamics/Circulant.lean`, line 27

```lean
/-- The Kuramoto field on `Cay(ℤ/n, S)`. -/
noncomputable def cField (K : ℝ) (θ : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  K / (#S : ℝ) * ∑ s ∈ S, sin (θ (i + s) - θ i)
```

### `twisted` — The twisted state θ_j = 2π a j/n.

`ArithmeticDynamics/Twisted.lean`, line 44

```lean
/-- The `a`-twisted state `θ_j = 2π a j / n`. -/
noncomputable def twisted (a : ℕ) : ZMod n → ℝ := fun x => 2 * π * a * x.val / n
```

### `jac` — Jacobian at a twisted state acting on complex vectors (Lemma 5.2).

`ArithmeticDynamics/Twisted.lean`, line 125

```lean
/-- The Jacobian of the Kuramoto model on `X_n` at the `m`-twisted state, acting on
functions `ℤ/n → ℂ`:  `(J f)_i = (K/φ(n)) ∑_u cos(2π m u/n) (f_{i+u} - f_i)`. -/
noncomputable def jac (K : ℝ) (m : ZMod n) (f : ZMod n → ℂ) (i : ZMod n) : ℂ :=
  ((K / (Nat.totient n : ℝ) : ℝ) : ℂ) * ∑ u : (ZMod n)ˣ, (twistWeight n m u : ℂ) * (f (i + u) - f i)
```

### `cJac` — Jacobian at a twisted state of a circulant, real form.

`ArithmeticDynamics/Circulant.lean`, line 37

```lean
/-- The real Jacobian of the circulant Kuramoto field at the `m`-twisted state. -/
noncomputable def cJac (K : ℝ) (m : ZMod n) (f : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  K / (#S : ℝ) * ∑ s ∈ S, cWeight m s * (f (i + s) - f i)
```

### `energy` — Energy E (5.2), whose negative gradient is the Kuramoto field.

`ArithmeticDynamics/Energy.lean`, line 16

```lean
/-- The Kuramoto energy `E(θ) = -(K/(2φ(n))) ∑_i ∑_u cos(θ_{i+u} - θ_i)` on `X_n`. -/
noncomputable def energy (n : ℕ) [NeZero n] (K : ℝ) (θ : ZMod n → ℝ) : ℝ :=
  -(K / (2 * (Nat.totient n : ℝ))) * ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, cos (θ (i + u) - θ i)
```

### `g` — The instability exponent g(M), equation (5.4).

`ArithmeticDynamics/Extremal.lean`, line 170

```lean
/-- `g M = (1 + r(M / gcd(2, M)))/2 - r M`; the Jacobian at a twisted state of order `M`
has the eigenvalue `K · g M` (Section 5.1 of the paper). -/
noncomputable def g (M : ℕ) : ℝ := (1 + r (M / Nat.gcd 2 M)) / 2 - r M
```

### `IsSolution` — A solution of ẋ = F(x): differentiable, with derivative F(x(t)) for all t.

`ArithmeticDynamics/Nonlinear.lean`, line 25

```lean
/-- `x` is a solution of `ẋ = F(x)` defined for all times. -/
def IsSolution (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (x : ℝ → ZMod n → ℝ) : Prop :=
  ∀ t, HasDerivAt x (F (x t)) t
```

### `LyapunovStable` — Lyapunov stability of an equilibrium.

`ArithmeticDynamics/Nonlinear.lean`, line 29

```lean
/-- Lyapunov stability of an equilibrium `xs`. -/
def LyapunovStable (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs : ZMod n → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, IsSolution F x → sqNorm (x 0 - xs) < δ →
    ∀ t ≥ 0, sqNorm (x t - xs) < ε
```

### `ExpStableOnLevel` — Local exponential stability with rate ρ on the invariant level set Σ x_i = Σ x*_i (stability modulo rotation).

`ArithmeticDynamics/Nonlinear.lean`, line 35

```lean
/-- Local exponential stability with rate `ρ` on the level set `∑ x = ∑ xs`
("modulo rotation" for the Kuramoto model). -/
def ExpStableOnLevel (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs : ZMod n → ℝ) (ρ : ℝ) : Prop :=
  ∃ δ > 0, ∀ x, IsSolution F x → ∑ j, x 0 j = ∑ j, xs j → sqNorm (x 0 - xs) < δ →
    ∀ t ≥ 0, sqNorm (x t - xs) ≤ Real.exp (-2 * ρ * t) * sqNorm (x 0 - xs)
```

### `LyapunovIndirectStability` — Hypothesis (H1).

`ArithmeticDynamics/Nonlinear.lean`, line 45

```lean
/-- **Lyapunov's indirect method (stability).**  For a `C¹`, globally Lipschitz field with zero
sum and an equilibrium whose linearisation is `≤ -r` on sum-zero vectors, the equilibrium is
exponentially stable with every rate `r' < r` on its level set. -/
def LyapunovIndirectStability : Prop :=
  ∀ (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs : ZMod n → ℝ) (r : ℝ),
    ContDiff ℝ 1 F → (∃ L, LipschitzWith L F) → F xs = 0 → (∀ x, ∑ j, F x j = 0) → 0 < r →
    (∀ w : ZMod n → ℝ, ∑ j, w j = 0 → ∑ j, fderiv ℝ F xs w j * w j ≤ -r * sqNorm w) →
    ∀ r', 0 < r' → r' < r → ExpStableOnLevel F xs r'
```

### `LyapunovIndirectInstability` — Hypothesis (H2).

`ArithmeticDynamics/Nonlinear.lean`, line 54

```lean
/-- **Lyapunov's instability theorem by first approximation.**  A real eigenvalue `μ > 0` of the
linearisation at an equilibrium of a `C¹`, globally Lipschitz field makes it unstable. -/
def LyapunovIndirectInstability : Prop :=
  ∀ (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs v : ZMod n → ℝ) (μ : ℝ),
    ContDiff ℝ 1 F → (∃ L, LipschitzWith L F) → F xs = 0 → v ≠ 0 →
    fderiv ℝ F xs v = μ • v → 0 < μ → ¬ LyapunovStable F xs
```

### `AbsilKurdyka` — Hypothesis (H3).

`ArithmeticDynamics/Nonlinear.lean`, line 62

```lean
/-- **Absil–Kurdyka.**  If `E` is real analytic and `F = -∇E` is `C¹` and globally Lipschitz,
then every Lyapunov-stable equilibrium of `ẋ = F(x)` is a local minimum of `E`. -/
def AbsilKurdyka : Prop :=
  ∀ (E : (ZMod n → ℝ) → ℝ) (F : (ZMod n → ℝ) → (ZMod n → ℝ)),
    (∀ x, AnalyticAt ℝ E x) →
    (∀ x v, HasDerivAt (fun t : ℝ => E (x + t • v)) (-∑ j, F x j * v j) 0) →
    ContDiff ℝ 1 F → (∃ L, LipschitzWith L F) →
    ∀ xs, F xs = 0 → LyapunovStable F xs → IsLocalMin E xs
```

## B. The classical hypotheses (H1)–(H3)

They are definitions of type `Prop`, not axioms, and appear as explicit arguments `(hL : LyapunovIndirectStability n)` etc. of the theorems that use them. Their statements are in Section A above. Each quantifies over every C¹, globally Lipschitz vector field on ℝ^{ℤ/n}.

## C. Results of the paper

### (2.3), (2.4)

`ramanujan_eq` (`Ramanujan.lean`, line 155)

```lean
/-- **Hölder's formula.**  `c_n(j) = φ(n) · μ(M)/φ(M)` with `M = ord(j)`. -/
theorem ramanujan_eq {n : ℕ} [NeZero n] (j : ZMod n) :
    ramanujan n j = (Nat.totient n : ℂ) * ((r (addOrderOf j) : ℝ) : ℂ)
```

`lap_chi` (`Spectrum.lean`, line 83)

```lean
/-- **Spectrum of `X_n`** (equation (2.4)): `L χ_k = φ(n)(1 - μ(M)/φ(M)) χ_k`, `M = ord k`. -/
theorem lap_chi (k i : ZMod n) : lap n (chi n k) i = ((lapEig n k : ℝ) : ℂ) * chi n k i
```

`lap_eigenvalue` (`Classification.lean`, line 167)

```lean
/-- **Completeness of the spectrum.**  Every eigenvalue of the Laplacian of `X_n` is one of
the numbers `λ(k) = φ(n)(1 - r(ord k))`; together with `lap_chi` this identifies the
spectrum of `X_n` exactly. -/
theorem lap_eigenvalue (f : ZMod n → ℂ) (c : ℂ) (hf : f ≠ 0)
    (h : ∀ i, lap n f i = c * f i) : ∃ k : ZMod n, c = ((lapEig n k : ℝ) : ℂ)
```

### (2.5)

`fiber_sum_eq_ramanujan` (`GcdGraph.lean`, line 174)

```lean
/-- **Equation (2.5).**  For `d ∣ n`, the sum of `e(ks/n)` over `gcd(s, n) = d` is the Ramanujan
sum `c_{n/d}(k)`. -/
theorem fiber_sum_eq_ramanujan {d : ℕ} (hd : d ∣ n) (hd0 : 0 < d) [NeZero (n / d)] (k : ZMod n) :
    ∑ s ∈ univ.filter (fun s : ZMod n => Nat.gcd s.val n = d), (ZMod.stdAddChar (k * s) : ℂ)
      = ramanujan (n / d) ((k.val : ℕ) : ZMod (n / d))
```

`cSym_gcd_int` (`GcdGraph.lean`, line 243)

```lean
/-- **Integrality.**  Every value `C_{S_D}(k)` of the symbol of a gcd graph is an integer. -/
theorem cSym_gcd_int (D : Finset ℕ) (k : ZMod n) : ∃ z : ℤ, cSym (gcdSet n D) k = z
```

### Lemma 3.1

`isLeast_divSet` (`Rates.lean`, line 35)

```lean
/-- **Lemma 3.1(i), sharp form.**  The least value is `-1/(p-1)`, `p = minFac n`. -/
theorem isLeast_divSet {n : ℕ} (hn : 2 ≤ n) :
    IsLeast (DivSet n) (-1 / ((n.minFac : ℝ) - 1))
```

`isGreatest_divSet_of_twoSmallest` (`Rates.lean`, line 79)

```lean
/-- **Lemma 3.1(ii), sharp form.** -/
theorem isGreatest_divSet_of_twoSmallest {n p q : ℕ} (h : TwoSmallest n p q) :
    IsGreatest (DivSet n) (1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)))
```

`isGreatest_divSet_prime` (`Rates.lean`, line 100)

```lean
/-- **Lemma 3.1(iv).** -/
theorem isGreatest_divSet_prime {p : ℕ} (hp : p.Prime) :
    IsGreatest (DivSet p) (-1 / ((p : ℝ) - 1))
```

`isGreatest_divSet_prime_pow` (`Rates.lean`, line 91)

```lean
/-- **Lemma 3.1(iii), sharp form.** -/
theorem isGreatest_divSet_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    IsGreatest (DivSet (p ^ a)) 0
```

`r_eq_min_iff` (`Multiplicity.lean`, line 40)

```lean
/-- **Lemma 3.1 (i), equality case.**  `r M = -1/(p-1)` for a divisor `M > 1` of `n` iff `M = p`. -/
theorem r_eq_min_iff {n M : ℕ} (hM : 1 < M) (hMn : M ∣ n) :
    r M = -1 / ((n.minFac : ℝ) - 1) ↔ M = n.minFac
```

`r_eq_max_iff` (`Multiplicity.lean`, line 99)

```lean
/-- **Lemma 3.1 (ii), equality case.**  If `p < q` are the two smallest prime divisors of `n`,
then `r M = 1/((p-1)(q-1))` for a divisor `M > 1` of `n` iff `M = p q`. -/
theorem r_eq_max_iff {n p q M : ℕ} (h : TwoSmallest n p q) (hM : 1 < M) (hMn : M ∣ n) :
    r M = 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)) ↔ M = p * q
```

### Theorem 3.2

`lapEig_le` (`Spectrum.lean`, line 116)

```lean
/-- **Theorem 3.2, upper bound.**  Every eigenvalue is at most `φ(n) p/(p-1)`, `p = minFac n`. -/
theorem lapEig_le (k : ZMod n) (hk : k ≠ 0) :
    lapEig n k ≤ (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1))
```

`lapEig_ge_prime_pow` (`Spectrum.lean`, line 165)

```lean
/-- **Theorem 3.2, lower bound for prime powers.** -/
theorem lapEig_ge_prime_pow {p a : ℕ} (hp : p.Prime) (hn : n = p ^ a) (k : ZMod n) (hk : k ≠ 0) :
    (Nat.totient n : ℝ) ≤ lapEig n k
```

`lapEig_ge_two_primes` (`Spectrum.lean`, line 148)

```lean
/-- **Theorem 3.2, lower bound when `ω(n) ≥ 2`.**  Here `p < q` are the two smallest prime
divisors of `n`. -/
theorem lapEig_ge_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hprimes : ∀ l : ℕ, l.Prime → l ∣ n → l = p ∨ q ≤ l) (k : ZMod n) (hk : k ≠ 0) :
    (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1))) ≤ lapEig n k
```

`card_lapEig_max` (`Multiplicity.lean`, line 243)

```lean
/-- **Theorem 3.2, multiplicity of `λ_max`.**  Exactly `p - 1` residues carry `λ_max`. -/
theorem card_lapEig_max (hn : 1 < n) :
    #(univ.filter (fun k : ZMod n =>
        lapEig n k = (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1))))
      = n.minFac - 1
```

`card_lapEig_prime_pow` (`Multiplicity.lean`, line 307)

```lean
/-- **Theorem 3.2, multiplicity of `λ₂` for `n = p^a`, `a ≥ 2`.**  Exactly `p^a - p` residues. -/
theorem card_lapEig_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (hn : n = p ^ a) :
    #(univ.filter (fun k : ZMod n => k ≠ 0 ∧ lapEig n k = (Nat.totient n : ℝ)))
      = p ^ a - p
```

`card_lapEig_two_primes` (`Multiplicity.lean`, line 279)

```lean
/-- **Theorem 3.2, multiplicity of `λ₂` when `ω(n) ≥ 2`.**  Exactly `(p-1)(q-1)` residues. -/
theorem card_lapEig_two_primes {p q : ℕ} (h : TwoSmallest n p q) :
    #(univ.filter (fun k : ZMod n =>
        k ≠ 0 ∧ lapEig n k = (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)))))
      = (p - 1) * (q - 1)
```

### Corollary 3.3

`spectral_ratio` (`Multiplicity.lean`, line 388)

```lean
/-- **Corollary 3.3.**  For every `n ≥ 2`, `λ₂/λ_max = (1 - r_max)/(1 - r_min) ≥ 1/4`,
with equality iff `6 ∣ n`. -/
theorem spectral_ratio {m : ℕ} (hm : 2 ≤ m) {rmax rmin : ℝ} (hmax : IsGreatest (DivSet m) rmax)
    (hmin : IsLeast (DivSet m) rmin) :
    1 / 4 ≤ (1 - rmax) / (1 - rmin) ∧ ((1 - rmax) / (1 - rmin) = 1 / 4 ↔ 6 ∣ m)
```

`spectral_ratio_formula` (`Multiplicity.lean`, line 371)

```lean
/-- **Corollary 3.3, formula.**  `λ₂/λ_max = ((p-1)(q-1) - 1)/(p(q-1))` when `ω(n) ≥ 2`. -/
theorem spectral_ratio_formula {p q : ℝ} (hp : 2 ≤ p) (hq : 3 ≤ q) :
    (1 - 1 / ((p - 1) * (q - 1))) / (1 - (-1 / (p - 1)))
      = ((p - 1) * (q - 1) - 1) / (p * (q - 1))
```

### Lemma 4.1

`contraction_of_opt_step` (`Consensus.lean`, line 15)

```lean
/-- **Lemma 4.1 (upper bound).**  With the step `ε = 2 / (a + b)` and the rate
`ρ = (b - a) / (a + b)`, every mode `l ∈ [a, b]` is contracted by at least `ρ`. -/
theorem contraction_of_opt_step {a b l ε ρ : ℝ} (hs : 0 < a + b)
    (hε : ε * (a + b) = 2) (hρ : ρ * (a + b) = b - a)
    (hl1 : a ≤ l) (hl2 : l ≤ b) : |1 - ε * l| ≤ ρ
```

`rate_lower_bound` (`Consensus.lean`, line 35)

```lean
/-- **Lemma 4.1 (optimality).**  No constant step does better than
`ρ = (b - a) / (a + b)` on the two extreme modes `a ≤ b`. -/
theorem rate_lower_bound {a b ε ρ : ℝ} (hs : 0 < a + b) (ha : 0 ≤ a) (hab : a ≤ b)
    (hρ : ρ * (a + b) = b - a) : ρ ≤ max |1 - ε * a| |1 - ε * b|
```

`sqNorm_err_iterate` (`ConsensusDynamics.lean`, line 58)

```lean
/-- **Lemma 4.1 / Theorem 4.3, the norm estimate.**  If `|1 - ε λ(k)| ≤ ρ` for all `k ≠ 0`, then
`‖x(t) - x̄ 1‖² ≤ ρ^{2t} ‖x(0) - x̄ 1‖²` for the iteration `x(t+1) = (I - εL) x(t)`. -/
theorem sqNorm_err_iterate {ε ρ : ℝ} (hρ : ∀ k : ZMod n, k ≠ 0 → |1 - ε * lapEig n k| ≤ ρ)
    (x : ZMod n → ℝ) (t : ℕ) :
    sqNorm (err ((step ε)^[t] x)) ≤ (ρ ^ 2) ^ t * sqNorm (err x)
```

### Theorem 4.3

`isRate_of_twoSmallest` (`Rates.lean`, line 169)

```lean
/-- **Theorem 4.3** for `n` with at least two prime divisors. -/
theorem isRate_of_twoSmallest {n p q : ℕ} (hn : 2 ≤ n) (h : TwoSmallest n p q) :
    IsRate n ((q : ℝ) / (2 * ((p : ℝ) - 1) * ((q : ℝ) - 1) + q - 2))
```

`isRate_prime_pow` (`Rates.lean`, line 183)

```lean
/-- **Theorem 4.3** for proper prime powers. -/
theorem isRate_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    IsRate (p ^ a) (1 / (2 * (p : ℝ) - 1))
```

`isRate_prime` (`Rates.lean`, line 197)

```lean
/-- **Theorem 4.3** for primes. -/
theorem isRate_prime {p : ℕ} (hp : p.Prime) : IsRate p 0
```

`opt_step_prime` (`ConsensusDynamics.lean`, line 196)

```lean
/-- **Theorem 4.3, the optimal step for `n` prime.** -/
theorem opt_step_prime {m : ℝ} (hm : 0 < m) : 2 / (m + m) = 1 / m
```

`opt_step_prime_pow` (`ConsensusDynamics.lean`, line 185)

```lean
/-- **Theorem 4.3, the optimal step for `n = p^a`, `a ≥ 2`.** -/
theorem opt_step_prime_pow {φ p : ℝ} (hφ : 0 < φ) (hp : 2 ≤ p) :
    2 / (φ + φ * (p / (p - 1))) = 2 * (p - 1) / ((2 * p - 1) * φ)
```

`opt_step_two_primes` (`ConsensusDynamics.lean`, line 171)

```lean
/-- **Theorem 4.3, the optimal step when `ω(n) ≥ 2`.** -/
theorem opt_step_two_primes {φ p q : ℝ} (hφ : 0 < φ) (hp : 2 ≤ p) (hq : 3 ≤ q) :
    2 / (φ * (1 - 1 / ((p - 1) * (q - 1))) + φ * (p / (p - 1)))
      = 2 * (p - 1) * (q - 1) / (φ * (2 * (p - 1) * (q - 1) + q - 2))
```

`consensus_of_isRate` (`ConsensusDynamics.lean`, line 81)

```lean
/-- **Theorem 4.3, dynamical form.**  If `ρ` is the optimal rate of `X_n` (`IsRate n ρ`), then the
iteration with the optimal step `ε* = 2/(λ₂ + λ_max)` satisfies
`‖x(t) - x̄ 1‖² ≤ ρ^{2t} ‖x(0) - x̄ 1‖²` for every initial vector. -/
theorem consensus_of_isRate {ρ : ℝ} (h : IsRate n ρ) :
    ∃ ε > 0, ∀ (x : ZMod n → ℝ) (t : ℕ),
      sqNorm (err ((step ε)^[t] x)) ≤ (ρ ^ 2) ^ t * sqNorm (err x)
```

### Corollary 4.5

`rate_le_and_eq_iff` (`Rates.lean`, line 203)

```lean
/-- **Corollary 4.5.**  For every `n ≥ 2` the optimal rate is at most `3/5`, with equality
if and only if `6 ∣ n`. -/
theorem rate_le_and_eq_iff {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (h : IsRate n ρ) :
    ρ ≤ 3 / 5 ∧ (ρ = 3 / 5 ↔ 6 ∣ n)
```

`consensus_three_fifths` (`ConsensusDynamics.lean`, line 133)

```lean
/-- **Corollary 4.5, dynamical form.**  On every unitary Cayley graph `X_n`, `n ≥ 2`, the
optimally tuned iteration satisfies `‖x(t) - x̄ 1‖ ≤ (3/5)^t ‖x(0) - x̄ 1‖`. -/
theorem consensus_three_fifths (hn : 2 ≤ n) :
    ∃ ε > 0, ∀ (x : ZMod n → ℝ) (t : ℕ),
      sqNorm (err ((step ε)^[t] x)) ≤ (((3 : ℝ) / 5) ^ 2) ^ t * sqNorm (err x)
```

`three_fifths_pow_le` (`ConsensusDynamics.lean`, line 145)

```lean
/-- **Corollary 4.5, iteration count.**  `(3/5)^t ≤ δ` as soon as `t ≥ log(1/δ)/log(5/3)`. -/
theorem three_fifths_pow_le {δ : ℝ} (hδ : 0 < δ) {t : ℕ}
    (ht : Real.log (1 / δ) / Real.log (5 / 3) ≤ t) : ((3 : ℝ) / 5) ^ t ≤ δ
```

### Remark 4.6

`rate_strictAnti_q` (`Remarks.lean`, line 17)

```lean
/-- For fixed `p`, the rate `q/(2(p-1)(q-1)+q-2)` is strictly decreasing in `q`. -/
theorem rate_strictAnti_q {p q₁ q₂ : ℝ} (hp : 2 ≤ p) (hq : 3 ≤ q₁) (hlt : q₁ < q₂) :
    q₂ / (2 * (p - 1) * (q₂ - 1) + q₂ - 2) < q₁ / (2 * (p - 1) * (q₁ - 1) + q₁ - 2)
```

`rate_tendsto_q` (`Remarks.lean`, line 25)

```lean
/-- For fixed `p`, the rate tends to `1/(2p-1)` as `q → ∞`, the value at the prime powers of `p`. -/
theorem rate_tendsto_q {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (fun q : ℝ => q / (2 * (p - 1) * (q - 1) + q - 2)) atTop (𝓝 (1 / (2 * p - 1)))
```

`rate_even` (`Remarks.lean`, line 51)

```lean
/-- **Remark 4.6, even moduli.**  For even `n > 2`, `1/3 ≤ ρ*(X_n) ≤ 3/5`. -/
theorem rate_even {m : ℕ} (hm : 2 < m) (heven : 2 ∣ m) {ρ : ℝ} (h : IsRate m ρ) :
    1 / 3 ≤ ρ ∧ ρ ≤ 3 / 5
```

`rate_odd` (`Remarks.lean`, line 78)

```lean
/-- **Remark 4.6, odd moduli.**  For odd `n ≥ 3`, `ρ*(X_n) ≤ 5/19`, with equality iff `15 ∣ n`. -/
theorem rate_odd {m : ℕ} (hm : 2 ≤ m) (hodd : ¬ 2 ∣ m) {ρ : ℝ} (h : IsRate m ρ) :
    ρ ≤ 5 / 19 ∧ (ρ = 5 / 19 ↔ 15 ∣ m)
```

### Proposition 4.7

`natural_step_factor` (`ConsensusDynamics.lean`, line 204)

```lean
/-- **Proposition 4.7, contraction factor.**  The non-trivial eigenvalues `r(ord k)` of
`I - L/φ(n) = A/φ(n)` have largest modulus exactly `1/(p-1)`. -/
theorem natural_step_factor (hn : 1 < n) :
    IsGreatest {y : ℝ | ∃ k : ZMod n, k ≠ 0 ∧ |r (addOrderOf k)| = y}
      (1 / ((n.minFac : ℝ) - 1))
```

`natural_step_lt_one_iff` (`ConsensusDynamics.lean`, line 220)

```lean
/-- **Proposition 4.7, convergence criterion.**  The factor `1/(p-1)` is `< 1` iff `n` is odd. -/
theorem natural_step_lt_one_iff (hn : 1 < n) :
    1 / ((n.minFac : ℝ) - 1) < 1 ↔ Odd n
```

`natural_step_even` (`ConsensusDynamics.lean`, line 267)

```lean
/-- **Proposition 4.7, non-convergence for even `n`.**  The alternating vector is a non-zero
sum-zero vector that the natural step maps to its negative, so its error never decays. -/
theorem natural_step_even (h2 : 2 ∣ n) :
    ∑ j, alternating n j = 0 ∧ alternating n ≠ 0 ∧
      step (1 / (Nat.totient n : ℝ)) (alternating n) = fun j => -alternating n j
```

### Remark 4.8 (continuous time)

`continuous_consensus` (`ConsensusDynamics.lean`, line 306)

```lean
/-- **Remark 4.8.**  For a solution of `ẋ = -L x` on `X_n` and any `a` with `a ≤ λ(k)` for all
`k ≠ 0`, `‖x(t) - x̄ 1‖² ≤ e^{-2at} ‖x(0) - x̄ 1‖²` for `t ≥ 0`. -/
theorem continuous_consensus {a : ℝ} (ha : ∀ k : ZMod n, k ≠ 0 → a ≤ lapEig n k)
    (x : ℝ → ZMod n → ℝ) (hx : ∀ t, HasDerivAt x (fun j => -lapR (x t) j) t) {t : ℝ}
    (ht : 0 ≤ t) :
    sqNorm (err (x t)) ≤ Real.exp (-2 * a * t) * sqNorm (err (x 0))
```

### Proposition 4.9

`mean_value` (`MeanValue.lean`, line 576)

```lean
/-- **Proposition 4.9 (mean value of the optimal consensus rate).**  The series defining
`meanRate` converges, and `(1/N) ∑_{n<N} ρ*(X_n) → meanRate`. -/
theorem mean_value :
    Summable pairWeight ∧
      Tendsto (fun N : ℕ => (∑ m ∈ range N, rhoStar m) / N) atTop (𝓝 meanRate)
```

`density_inA` (`MeanValue.lean`, line 246)

```lean
/-- **The density of `A_{p,q}`.**  For primes `p < q ≤ y`, the proportion of `m < Q_y` in
`A_{p,q}` is exactly `dens p q`. -/
theorem density_inA {y p q : ℕ} (hpq : (p, q) ∈ pairsUpTo y) :
    (#((range (Qy y)).filter (InA p q)) : ℝ) / (Qy y) = dens p q
```

`density_inE_le` (`MeanValue.lean`, line 403)

```lean
/-- **The exceptional set is small.**  Its proportion in a period is at most
`e^{-S}(1 + 2S)`, `S = ∑_{p ≤ y} 1/p`. -/
theorem density_inE_le (y : ℕ) :
    (#((range (Qy y)).filter (InE y)) : ℝ) / (Qy y)
      ≤ Real.exp (-∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ)) * (1 + 2 * ∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ))
```

### Lemma 5.2

`kuramotoField_twisted` (`Twisted.lean`, line 90)

```lean
/-- **Lemma 5.2 (i).**  Every twisted state is an equilibrium of the Kuramoto model on `X_n`. -/
theorem kuramotoField_twisted (K : ℝ) (a : ℕ) (i : ZMod n) :
    kuramotoField n K (twisted n a) i = 0
```

`fderiv_kuramotoField` (`Energy.lean`, line 143)

```lean
/-- **Lemma 5.2 (ii).**  The Fréchet derivative of the Kuramoto field on `X_n`:
`(DF(θ) f)_i = (K/φ(n)) ∑_u cos(θ_{i+u} - θ_i)(f_{i+u} - f_i)`. -/
theorem fderiv_kuramotoField (K : ℝ) (θ f : ZMod n → ℝ) (i : ZMod n) :
    fderiv ℝ (kuramotoField n K) θ f i
      = K / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, cos (θ (i + u) - θ i) * (f (i + u) - f i)
```

`jac_chi` (`Twisted.lean`, line 177)

```lean
/-- **Lemma 5.2 (iii).**  `J χ_k = K · μ_k/φ(n) · χ_k` with
`μ_k/φ(n) = (r(ord(m+k)) + r(ord(m-k)))/2 - r(ord m)`  (equation (5.5)). -/
theorem jac_chi (K : ℝ) (m k i : ZMod n) :
    jac n K m (chi n k) i
      = ((K * ((r (addOrderOf (m + k)) + r (addOrderOf (m - k))) / 2 - r (addOrderOf m)) : ℝ) : ℂ)
          * chi n k i
```

### Lemma 5.3

`g_one` (`Remarks.lean`, line 284)

```lean
/-- **Lemma 5.3.**  `g(1) = 0`. -/
theorem g_one : g 1 = 0
```

`g_two` (`Extremal.lean`, line 194)

```lean
/-- **Lemma 5.3.**  `g(2) = 2`. -/
theorem g_two : g 2 = 2
```

`g_four` (`Extremal.lean`, line 200)

```lean
/-- **Lemma 5.3.**  `g(4) = 0`. -/
theorem g_four : g 4 = 0
```

`g_six` (`Extremal.lean`, line 206)

```lean
/-- **Lemma 5.3.**  `g(6) = -1/4`. -/
theorem g_six : g 6 = -1 / 4
```

`g_ge` (`Extremal.lean`, line 259)

```lean
/-- **Lemma 5.3.**  `g M ≥ 1/8` for every `M ≥ 2` other than `4` and `6`. -/
theorem g_ge {M : ℕ} (hM : 2 ≤ M) (h4 : M ≠ 4) (h6 : M ≠ 6) : 1 / 8 ≤ g M
```

### Theorem 5.4

`twisted_classification` (`Classification.lean`, line 117)

```lean
/-- **Theorem 5.4 (classification of twisted states on `X_n`).**  Let `m ≠ 0` have additive
order `M`.
* If `M = 6`, every character `χ_k`, `k ≠ 0`, is an eigenvector of the Jacobian with a real
  eigenvalue at most `-K/4` (linear stability).
* If `M = 4`, the Jacobian is the zero operator.
* Otherwise `χ_m` is an eigenvector with real eigenvalue at least `K/8 > 0` (instability). -/
theorem twisted_classification {K : ℝ} (hK : 0 < K) {m : ZMod n} (hm : m ≠ 0) :
    (addOrderOf m = 6 → ∀ k : ZMod n, k ≠ 0 →
        ∃ ev : ℝ, ev ≤ -(K / 4) ∧ ∀ i, jac n K m (chi n k) i = (ev : ℂ) * chi n k i) ∧
    (addOrderOf m = 4 → ∀ (f : ZMod n → ℂ) (i : ZMod n), jac n K m f i = 0) ∧
    (addOrderOf m ≠ 4 → addOrderOf m ≠ 6 →
        ∃ ev : ℝ, K / 8 ≤ ev ∧ ∀ i, jac n K m (chi n m) i = (ev : ℂ) * chi n m i)
```

`twisted_unstable_nonlinear` (`Nonlinear.lean`, line 261) — uses H2

```lean
/-- **Theorem 5.4 (c), nonlinear form.**  If `m ≠ 0` has order `∉ {4, 6}`, the `m`-twisted state
is (Lyapunov) unstable. -/
theorem twisted_unstable_nonlinear (hI : LyapunovIndirectInstability n) {K : ℝ} (hK : 0 < K)
    {a : ℕ} (hm : (a : ZMod n) ≠ 0) (h4 : addOrderOf (a : ZMod n) ≠ 4)
    (h6 : addOrderOf (a : ZMod n) ≠ 6) :
    ¬ LyapunovStable (kuramotoField n K) (twisted n a)
```

### Theorem 5.5

`jac_hex` (`Twisted.lean`, line 256)

```lean
/-- **Theorem 5.5.**  At the hexagonal state the Jacobian is `-(K/(2φ(n)))` times the
Laplacian of `X_n`; hence its spectrum is `-(K/2)(1 - r(M))`, contained in `[-K, -K/4]`
by Theorem 3.2. -/
theorem jac_hex (h6 : 6 ∣ n) (K : ℝ) (f : ZMod n → ℂ) (i : ZMod n) :
    jac n K ((n / 6 : ℕ) : ZMod n) f i
      = -((K / (2 * (Nat.totient n : ℝ)) : ℝ) : ℂ) * lap n f i
```

`jac_hex_five` (`Nonlinear.lean`, line 175)

```lean
/-- **Theorem 5.5 for `m = 5n/6`.**  The Jacobian at `m = 5n/6` equals the Jacobian at `m = n/6`,
namely `-(K/(2φ(n)))` times the Laplacian of `X_n`. -/
theorem jac_hex_five (h6 : 6 ∣ n) (K : ℝ) (f : ZMod n → ℂ) (i : ZMod n) :
    jac n K ((5 * (n / 6) : ℕ) : ZMod n) f i
      = -((K / (2 * (Nat.totient n : ℝ)) : ℝ) : ℂ) * lap n f i
```

`hex_spectrum` (`Nonlinear.lean`, line 209)

```lean
/-- **Theorem 5.5, spectrum.**  The eigenvalues `-(K/2)(1 - r(ord k))`, `k ≠ 0`, of the hexagonal
Jacobian lie in `[-K, -K/4]`, and `-K/4` is attained exactly at the residues of order `6`. -/
theorem hex_spectrum (h6 : 6 ∣ n) {K : ℝ} (hK : 0 < K) (k : ZMod n) (hk : k ≠ 0) :
    -K ≤ -(K / 2) * (1 - r (addOrderOf k)) ∧ -(K / 2) * (1 - r (addOrderOf k)) ≤ -(K / 4) ∧
      (-(K / 2) * (1 - r (addOrderOf k)) = -(K / 4) ↔ addOrderOf k = 6)
```

`hex_expStable` (`Nonlinear.lean`, line 137) — uses H1

```lean
/-- **Theorem 5.5.**  For `6 ∣ n` the hexagonal state is exponentially stable modulo rotation
with every rate `r' < K/4`. -/
theorem hex_expStable (hL : LyapunovIndirectStability n) (h6 : 6 ∣ n) {K : ℝ} (hK : 0 < K)
    {r' : ℝ} (hr' : 0 < r') (hr : r' < K / 4) :
    ExpStableOnLevel (kuramotoField n K) (twisted n (n / 6)) r'
```

`hex_expStable_five` (`Nonlinear.lean`, line 184) — uses H1

```lean
/-- **Theorem 5.5 for `m = 5n/6`.**  For `6 ∣ n` the hexagonal state `θ_j = -jπ/3` (that is,
`m = 5n/6`) is exponentially stable modulo rotation with every rate `r' < K/4`. -/
theorem hex_expStable_five (hL : LyapunovIndirectStability n) (h6 : 6 ∣ n) {K : ℝ} (hK : 0 < K)
    {r' : ℝ} (hr' : 0 < r') (hr : r' < K / 4) :
    ExpStableOnLevel (kuramotoField n K) (twisted n (5 * (n / 6))) r'
```

`sync_expStable` (`Nonlinear.lean`, line 148) — uses H1

```lean
/-- **Theorem 5.5 (synchronous state).**  The synchronous state is exponentially stable modulo
rotation with every rate `r' < K/2`. -/
theorem sync_expStable (hL : LyapunovIndirectStability n) {K : ℝ} (hK : 0 < K)
    {r' : ℝ} (hr' : 0 < r') (hr : r' < K / 2) :
    ExpStableOnLevel (kuramotoField n K) (twisted n 0) r'
```

### Theorem 5.6

`jac_quarter` (`Twisted.lean`, line 315)

```lean
/-- **Theorem 5.6 (i).**  The Jacobian at a quarter twist vanishes identically. -/
theorem jac_quarter (h4 : 4 ∣ n) (K : ℝ) (f : ZMod n → ℂ) (i : ZMod n) :
    jac n K ((n / 4 : ℕ) : ZMod n) f i = 0
```

`energy_quarter_kick` (`Energy.lean`, line 375)

```lean
/-- **Theorem 5.6 (ii) for `m = n/4`.** -/
theorem energy_quarter_kick (h4 : 4 ∣ n) (K t : ℝ) :
    energy n K (twisted n (n / 4) + kick n t)
      = 2 * K / (Nat.totient n : ℝ) * sin t * (1 - cos t)
```

`energy_three_quarter_kick` (`Energy.lean`, line 383)

```lean
/-- **Theorem 5.6 (ii) for `m = 3n/4`.** -/
theorem energy_three_quarter_kick (h4 : 4 ∣ n) (K t : ℝ) :
    energy n K (twisted n (3 * (n / 4)) + kick n t)
      = -(2 * K / (Nat.totient n : ℝ) * sin t * (1 - cos t))
```

`quarter_not_isLocalMin` (`Nonlinear.lean`, line 345)

```lean
/-- **Theorem 5.6 (iii).**  The quarter twist `m = n/4` is not a local minimum of the energy. -/
theorem quarter_not_isLocalMin (h4 : 4 ∣ n) {K : ℝ} (hK : 0 < K) :
    ¬ IsLocalMin (energy n K) (twisted n (n / 4))
```

`three_quarter_not_isLocalMin` (`Nonlinear.lean`, line 352)

```lean
/-- **Theorem 5.6 (iii).**  The quarter twist `m = 3n/4` is not a local minimum of the energy. -/
theorem three_quarter_not_isLocalMin (h4 : 4 ∣ n) {K : ℝ} (hK : 0 < K) :
    ¬ IsLocalMin (energy n K) (twisted n (3 * (n / 4)))
```

`quarter_unstable` (`Nonlinear.lean`, line 359) — uses H3

```lean
/-- **Theorem 5.6 (iii).**  Under Absil–Kurdyka, the quarter twists are unstable. -/
theorem quarter_unstable (hAK : AbsilKurdyka n) (h4 : 4 ∣ n) {K : ℝ} (hK : 0 < K) :
    ¬ LyapunovStable (kuramotoField n K) (twisted n (n / 4)) ∧
      ¬ LyapunovStable (kuramotoField n K) (twisted n (3 * (n / 4)))
```

### Corollary 5.7

`linearly_stable_iff` (`Nonlinear.lean`, line 378)

```lean
/-- **Corollary 5.7.**  For `m ≠ 0`, the `m`-twisted state is linearly stable (every non-trivial
character is an eigenvector with a negative eigenvalue) iff `m` has order `6`. -/
theorem linearly_stable_iff {K : ℝ} (hK : 0 < K) {m : ZMod n} (hm : m ≠ 0) :
    (∀ k : ZMod n, k ≠ 0 → ∃ ev : ℝ, ev < 0 ∧ ∀ i, jac n K m (chi n k) i = (ev : ℂ) * chi n k i)
      ↔ addOrderOf m = 6
```

`exists_order_six_iff` (`Nonlinear.lean`, line 400)

```lean
/-- **Corollary 5.7.**  `X_n` has a non-zero twist of order `6` iff `6 ∣ n`. -/
theorem exists_order_six_iff : (∃ m : ZMod n, m ≠ 0 ∧ addOrderOf m = 6) ↔ 6 ∣ n
```

### Remarks in Section 5

`twistWeight_hex` (`Twisted.lean`, line 234)

```lean
/-- At the hexagonal state `m = n/6` every edge weight is `cos(π/3) = 1/2`. -/
theorem twistWeight_hex (h6 : 6 ∣ n) (u : (ZMod n)ˣ) :
    twistWeight n ((n / 6 : ℕ) : ZMod n) u = 1 / 2
```

`totient_le_third` (`Remarks.lean`, line 153)

```lean
/-- **Remark 5.9.**  If `6 ∣ n`, then `3 φ(n) ≤ n`, with equality iff the only prime divisors of
`n` are `2` and `3`. -/
theorem totient_le_third {m : ℕ} (hm0 : m ≠ 0) (h6 : 6 ∣ m) :
    3 * Nat.totient m ≤ m ∧ (3 * Nat.totient m = m ↔ m.primeFactors = {2, 3})
```

`relative_degree_lt` (`Remarks.lean`, line 202)

```lean
/-- **Remark 5.9.**  For `6 ∣ n`, the relative degree of `X_n` is below the `75%` density
threshold: `φ(n)/(n-1) < 3/4`. -/
theorem relative_degree_lt {m : ℕ} (hm0 : m ≠ 0) (h6 : 6 ∣ m) :
    (Nat.totient m : ℝ) / ((m : ℝ) - 1) < 3 / 4
```

### Proposition 6.1

`circulant_unstable_linear` (`Circulant.lean`, line 268)

```lean
/-- **Proposition 6.1 (i).**  If `C(m) < (|S| + C(2m))/2`, then `Re χ_m` is a non-zero real
eigenvector of the Jacobian at the `m`-twisted state with positive eigenvalue. -/
theorem circulant_unstable_linear (hS : IsSymm S) {K : ℝ} (hK : 0 < K) (hSne : S.Nonempty)
    (m : ZMod n) (hcond : cSym S m < ((#S : ℝ) + cSym S (m + m)) / 2) :
    0 < K / (#S : ℝ) * (((#S : ℝ) + cSym S (m + m)) / 2 - cSym S m) ∧
      (fun j => (chi n m j).re) ≠ 0 ∧
      ∀ i, cJac S K m (fun j => (chi n m j).re) i
        = K / (#S : ℝ) * (((#S : ℝ) + cSym S (m + m)) / 2 - cSym S m) * (chi n m i).re
```

`circulant_unstable` (`Circulant.lean`, line 294) — uses H2

```lean
/-- **Proposition 6.1 (i), nonlinear form.** -/
theorem circulant_unstable (hI : LyapunovIndirectInstability n) (hS : IsSymm S) {K : ℝ}
    (hK : 0 < K) (hSne : S.Nonempty) (a : ℕ)
    (hcond : cSym S (a : ZMod n) < ((#S : ℝ) + cSym S ((a : ZMod n) + a)) / 2) :
    ¬ LyapunovStable (cField S K) (twisted n a)
```

`circulant_stable_linear` (`Circulant.lean`, line 330)

```lean
/-- **Proposition 6.1 (ii).**  If `S` generates `ℤ/n` and every edge weight at the `m`-twisted
state is positive, the Jacobian is negative definite on non-zero sum-zero vectors. -/
theorem circulant_stable_linear {K : ℝ} (hK : 0 < K)
    (hgen : AddSubgroup.closure (S : Set (ZMod n)) = ⊤) (m : ZMod n)
    (hpos : ∀ s ∈ S, 0 < cWeight m s) (w : ZMod n → ℝ) (hw : ∑ j, w j = 0) (hw0 : w ≠ 0) :
    ∑ j, cJac S K m w j * w j < 0
```

### Proposition 6.2

`cJac_hex_gcd` (`GcdGraph.lean`, line 64)

```lean
/-- **Proposition 6.2, Jacobian.**  `J = -(K/(2|S_D|)) L_D` at the hexagonal state. -/
theorem cJac_hex_gcd (h6 : 6 ∣ n) {D : Finset ℕ} (hD6 : ∀ d ∈ D, Nat.Coprime d 6) (K : ℝ)
    (f : ZMod n → ℝ) (i : ZMod n) :
    cJac (gcdSet n D) K ((n / 6 : ℕ) : ZMod n) f i
      = -(K / (2 * (#(gcdSet n D) : ℝ))) * cLap (gcdSet n D) f i
```

`gcd_hex_expStable` (`GcdGraph.lean`, line 120) — uses H1

```lean
/-- **Proposition 6.2.**  If `6 ∣ n`, every `d ∈ D` is coprime to `6` and `X_n(D)` is connected,
the hexagonal state is exponentially stable modulo rotation with every rate below
`K λ₂(L_D)/(2|S_D|)`, and `λ₂(L_D) > 0`. -/
theorem gcd_hex_expStable (hL : LyapunovIndirectStability n) (h6 : 6 ∣ n) {D : Finset ℕ}
    (hD6 : ∀ d ∈ D, Nat.Coprime d 6)
    (hgen : AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) = ⊤)
    {K : ℝ} (hK : 0 < K) (hn : 1 < n) :
    0 < lam2 (gcdSet n D) hn ∧
      ∀ r', 0 < r' → r' < K * lam2 (gcdSet n D) hn / (2 * (#(gcdSet n D) : ℝ)) →
        ExpStableOnLevel (cField (gcdSet n D) K) (twisted n (n / 6)) r'
```

`gcd_sync_expStable` (`GcdGraph.lean`, line 146) — uses H1

```lean
/-- **Proposition 6.2, synchronous state.**  On a connected gcd graph the synchronous state is
exponentially stable modulo rotation with every rate below `K λ₂(L_D)/|S_D|` (twice the
hexagonal bound). -/
theorem gcd_sync_expStable (hL : LyapunovIndirectStability n) {D : Finset ℕ}
    (hgen : AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) = ⊤)
    {K : ℝ} (hK : 0 < K) (hn : 1 < n) :
    ∀ r', 0 < r' → r' < K * lam2 (gcdSet n D) hn / (#(gcdSet n D) : ℝ) →
      ExpStableOnLevel (cField (gcdSet n D) K) (twisted n 0) r'
```

### Remark in Section 6

`cJac_quarter_gcd` (`Remarks.lean`, line 278)

```lean
/-- **Remark 6.3, quarter twists on gcd graphs.**  If `4 ∣ n` and every element of `D` is odd, the
Jacobian at the quarter twist `m = n/4` of `X_n(D)` vanishes. -/
theorem cJac_quarter_gcd (h4 : 4 ∣ n) {D : Finset ℕ} (hDodd : ∀ d ∈ D, Odd d) (K : ℝ)
    (f : ZMod n → ℝ) (i : ZMod n) : cJac (gcdSet n D) K ((n / 4 : ℕ) : ZMod n) f i = 0
```

`cos_hex_cases` (`Remarks.lean`, line 215)

```lean
/-- The phase lag `π s/3` across an edge of step `s` at the hexagonal state has cosine `1`, `1/2`,
`-1/2` or `-1` according to `gcd(s, 6) = 6, 1, 2, 3`. -/
theorem cos_hex_cases (s : ℤ) :
    (6 ∣ s → cos (π * s / 3) = 1) ∧
    (¬ 2 ∣ s → ¬ 3 ∣ s → cos (π * s / 3) = 1 / 2) ∧
    (2 ∣ s → ¬ 3 ∣ s → cos (π * s / 3) = -1 / 2) ∧
    (¬ 2 ∣ s → 3 ∣ s → cos (π * s / 3) = -1)
```

### Proposition 6.4(i)

`gcd_connected_iff` (`GcdConsensus.lean`, line 372)

```lean
/-- **Proposition 6.4 (i): connectivity of gcd graphs.**  For a set `D` of proper divisors of `n ≥ 2`, the gcd graph
`X_n(D)` is connected if and only if `gcd(D) = 1`. -/
theorem gcd_connected_iff (hn : 1 < n) {D : Finset ℕ} (hD : ProperDivisors n D) :
    AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) = ⊤ ↔ D.gcd id = 1
```

`lam2_pos_iff` (`GcdConsensus.lean`, line 304)

```lean
/-- `λ₂ > 0` exactly when `S` generates `ℤ/n`, i.e. when the circulant is connected. -/
theorem lam2_pos_iff (hS : IsSymm S) (hn : 1 < n) :
    0 < lam2 S hn ↔ AddSubgroup.closure (S : Set (ZMod n)) = ⊤
```

### Proposition 6.4(ii)

`gcd_rate` (`GcdGraph.lean`, line 288)

```lean
/-- **Extreme eigenvalues of a gcd graph** (used in Proposition 6.4).  For every gcd graph
`X_n(D)`, `n ≥ 2`, with `C⁺ = max_{k≠0} C(k)` and `C⁻ = min_{k≠0} C(k)`, every non-trivial
Laplacian eigenvalue `|S| - C(k)` lies in `[|S| - C⁺, |S| - C⁻]`, both ends are attained, the
quotient `(λ_max - λ₂)/(λ_max + λ₂)` equals `(C⁺ - C⁻)/(2|S| - C⁺ - C⁻)`, and this number is
rational.  No connectivity is assumed here; the dynamical statements, which do need it, are
`gcd_consensus` (connected) and `gcd_no_consensus` (disconnected) in `GcdConsensus.lean`. -/
theorem gcd_rate (D : Finset ℕ) (hn : 1 < n) :
    let S := gcdSet n D
    let ne : (univ.erase (0 : ZMod n)).Nonempty :=
      ⟨1, mem_erase.mpr ⟨by haveI : Fact (1 < n) := ⟨hn⟩; exact one_ne_zero, mem_univ _⟩⟩
    let Cp := (univ.erase (0 : ZMod n)).sup' ne (cSym S)
    let Cm := (univ.erase (0 : ZMod n)).inf' ne (cSym S)
    (∀ k : ZMod n, k ≠ 0 →
        (#S : ℝ) - Cp ≤ (#S : ℝ) - cSym S k ∧ (#S : ℝ) - cSym S k ≤ (#S : ℝ) - Cm) ∧
      (∃ k, k ≠ 0 ∧ cSym S k = Cp) ∧ (∃ k, k ≠ 0 ∧ cSym S k = Cm) ∧
      (((#S : ℝ) - Cm) - ((#S : ℝ) - Cp)) / (((#S : ℝ) - Cm) + ((#S : ℝ) - Cp))
        = (Cp - Cm) / (2 * #S - Cp - Cm) ∧
      ∃ q : ℚ, (Cp - Cm) / (2 * (#S : ℝ) - Cp - Cm) = q
```

`ramanujan_int` (`GcdGraph.lean`, line 227)

```lean
/-- Ramanujan sums are integers. -/
theorem ramanujan_int (N : ℕ) [NeZero N] (j : ZMod N) : ∃ z : ℤ, ramanujan N j = z
```

`gcd_consensus` (`GcdConsensus.lean`, line 434)

```lean
/-- **Proposition 6.4 (ii): the connected case.**  Let `n ≥ 2` and let `D` be a set of proper divisors
of `n` with `gcd(D) = 1`, so that `X_n(D)` is connected.  Put `C⁺ = max_{k≠0} C(k)` and
`C⁻ = min_{k≠0} C(k)`.  Then `λ₂ = |S| - C⁺ > 0`, the optimal rate
`ρ* = (C⁺ - C⁻)/(2|S| - C⁺ - C⁻)` lies in `[0, 1)`, the iteration with step
`ε* = 2/(2|S| - C⁺ - C⁻)` satisfies `‖x(t) - x̄ 1‖² ≤ ρ*^{2t} ‖x(0) - x̄ 1‖²` and reaches
consensus from every initial vector, and for every constant step `ε` some non-constant initial
vector decays no faster than `ρ*^t`. -/
theorem gcd_consensus (hn : 1 < n) {D : Finset ℕ} (hD : ProperDivisors n D)
    (hgcd : D.gcd id = 1) :
    let S := gcdSet n D
    let ne : (univ.erase (0 : ZMod n)).Nonempty :=
      ⟨1, mem_erase.mpr ⟨by haveI : Fact (1 < n) := ⟨hn⟩; exact one_ne_zero, mem_univ _⟩⟩
    let Cp := (univ.erase (0 : ZMod n)).sup' ne (cSym S)
    let Cm := (univ.erase (0 : ZMod n)).inf' ne (cSym S)
    let ρ := (Cp - Cm) / (2 * (#S : ℝ) - Cp - Cm)
    lam2 S hn = (#S : ℝ) - Cp ∧ 0 < (#S : ℝ) - Cp ∧
    0 ≤ ρ ∧ ρ < 1 ∧
    (∀ x : ZMod n → ℝ,
      (∀ t : ℕ, sqNorm (err ((cStep S (2 / (2 * (#S : ℝ) - Cp - Cm)))^[t] x))
          ≤ (ρ ^ 2) ^ t * sqNorm (err x)) ∧
      Tendsto (fun t : ℕ => sqNorm (err ((cStep S (2 / (2 * (#S : ℝ) - Cp - Cm)))^[t] x)))
        atTop (𝓝 0)) ∧
    ∀ ε : ℝ, ∃ x : ZMod n → ℝ, err x ≠ 0 ∧
      ∀ t : ℕ, (ρ ^ 2) ^ t * sqNorm (err x) ≤ sqNorm (err ((cStep S ε)^[t] x))
```

`circulant_consensus` (`GcdConsensus.lean`, line 199)

```lean
/-- **Consensus on a circulant with spectral bounds `0 < a ≤ λ(k) ≤ b` (`k ≠ 0`).**  With the
step `ε* = 2/(a+b)` the error contracts at rate `ρ = (b-a)/(a+b) < 1` and tends to zero. -/
theorem circulant_consensus (hS : IsSymm S) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hk : ∀ k : ZMod n, k ≠ 0 → a ≤ (#S : ℝ) - cSym S k ∧ (#S : ℝ) - cSym S k ≤ b) :
    0 ≤ (b - a) / (a + b) ∧ (b - a) / (a + b) < 1 ∧
    ∀ x : ZMod n → ℝ,
      (∀ t : ℕ, sqNorm (err ((cStep S (2 / (a + b)))^[t] x))
          ≤ (((b - a) / (a + b)) ^ 2) ^ t * sqNorm (err x)) ∧
      Tendsto (fun t : ℕ => sqNorm (err ((cStep S (2 / (a + b)))^[t] x))) atTop (𝓝 0)
```

`circulant_mode_exact` (`GcdConsensus.lean`, line 176)

```lean
/-- **Exactness of a mode.**  For `k ≠ 0` the real mode `cos(2π k j/n)` is a non-constant initial
vector whose consensus error decays exactly by the factor `|1 - ε(|S| - C(k))|` per step. -/
theorem circulant_mode_exact (hS : IsSymm S) {k : ZMod n} (hk : k ≠ 0) (ε : ℝ) :
    err (cosMode k) ≠ 0 ∧ ∀ t : ℕ,
      sqNorm (err ((cStep S ε)^[t] (cosMode k)))
        = ((1 - ε * ((#S : ℝ) - cSym S k)) ^ 2) ^ t * sqNorm (err (cosMode k))
```

### Proposition 6.4(iii)

`gcd_no_consensus` (`GcdConsensus.lean`, line 514)

```lean
/-- **Proposition 6.4 (iii): the disconnected case.**  If `gcd(D) ≠ 1`, then `X_n(D)` is disconnected,
`λ₂ = 0`, and there is a non-constant initial vector that every constant-step iteration leaves
fixed, so global consensus does not occur from it. -/
theorem gcd_no_consensus (hn : 1 < n) {D : Finset ℕ} (hD : ProperDivisors n D)
    (hgcd : D.gcd id ≠ 1) :
    AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) ≠ ⊤ ∧
    lam2 (gcdSet n D) hn = 0 ∧
    ∃ x : ZMod n → ℝ, err x ≠ 0 ∧
      (∀ (ε : ℝ) (t : ℕ), (cStep (gcdSet n D) ε)^[t] x = x) ∧
      ∀ ε : ℝ, ¬ Tendsto (fun t : ℕ => sqNorm (err ((cStep (gcdSet n D) ε)^[t] x))) atTop (𝓝 0)
```

`circulant_no_consensus` (`GcdConsensus.lean`, line 270)

```lean
/-- **No consensus on a disconnected circulant.**  If every element of `S` lies in the proper
subgroup `g ℤ/n` (`1 < g ∣ n`), then `λ₂ = 0`, and the indicator of that subgroup is a
non-constant vector fixed by every step of the iteration, so its consensus error never decays. -/
theorem circulant_no_consensus (hS : IsSymm S) (hn : 1 < n) {g : ℕ} (hg1 : 1 < g)
    (hgn : g ∣ n) (hgS : ∀ s ∈ S, g ∣ s.val) :
    lam2 S hn = 0 ∧ err (subIndicator n g) ≠ 0 ∧
      ∀ (ε : ℝ) (t : ℕ), (cStep S ε)^[t] (subIndicator n g) = subIndicator n g
```

### Example 6.5

`gcd_example_six_two` (`GcdConsensus.lean`, line 551)

```lean
/-- **Example 6.5.**  For `n = 6` and `D = {2}` the gcd graph is two disjoint triangles:
it is disconnected, `λ₂ = 0`, and consensus fails from a non-constant initial vector. -/
theorem gcd_example_six_two :
    AddSubgroup.closure ((gcdSet 6 {2} : Finset (ZMod 6)) : Set (ZMod 6)) ≠ ⊤ ∧
    lam2 (gcdSet 6 {2}) (by norm_num) = 0 ∧
    ∃ x : ZMod 6 → ℝ, err x ≠ 0 ∧ ∀ (ε : ℝ) (t : ℕ), (cStep (gcdSet 6 {2}) ε)^[t] x = x
```
