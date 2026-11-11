/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs:
exact consensus rates and twisted states from Ramanujan sums

Complete Lean 4 formalisation in a single file: 19 parts, 312 theorems.
Verified with Lean v4.36.0-rc2 and Mathlib commit 2ddf59c8f142.
No `sorry`; every theorem depends only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.

Classical results used as hypotheses (Part XVI, `Nonlinear`): three theorems from the stability
theory of ordinary differential equations are stated as the propositions
`LyapunovIndirectStability`, `LyapunovIndirectInstability` and `AbsilKurdyka`, each for every
vector field on `ℝ^{ℤ/n}` satisfying the standard assumptions, and are taken as explicit
hypotheses of the nonlinear stability theorems that use them. Nothing else is assumed.

The only import needed is `Mathlib`. To run online, paste into https://live.lean-lang.org
-/
import Mathlib

/-! ════════════════════════ Part 1: Consensus ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part I: the algebra behind the optimal consensus rate (Section 4 of the paper).

All statements are division-free: a quotient `x = u / v` is encoded by the
hypothesis `x * v = u`.  This keeps every proof inside `linear_combination`
and `nlinarith`.
-/

namespace ArithmeticDynamics

/-- **Lemma 4.1 (upper bound).**  With the step `ε = 2 / (a + b)` and the rate
`ρ = (b - a) / (a + b)`, every mode `l ∈ [a, b]` is contracted by at least `ρ`. -/
theorem contraction_of_opt_step {a b l ε ρ : ℝ} (hs : 0 < a + b)
    (hε : ε * (a + b) = 2) (hρ : ρ * (a + b) = b - a)
    (hl1 : a ≤ l) (hl2 : l ≤ b) : |1 - ε * l| ≤ ρ := by
  have e1 : (a + b) * (1 - ε * l) = (a + b) - 2 * l := by
    linear_combination (-l) * hε
  have e2 : (a + b) * ρ = b - a := by
    linear_combination hρ
  have e3 : (a + b) * (-ρ) = a - b := by
    linear_combination (-1 : ℝ) * hρ
  rw [abs_le]
  constructor
  · refine le_of_mul_le_mul_left ?_ hs
    rw [e3, e1]
    linarith
  · refine le_of_mul_le_mul_left ?_ hs
    rw [e1, e2]
    linarith

/-- **Lemma 4.1 (optimality).**  No constant step does better than
`ρ = (b - a) / (a + b)` on the two extreme modes `a ≤ b`. -/
theorem rate_lower_bound {a b ε ρ : ℝ} (hs : 0 < a + b) (ha : 0 ≤ a) (hab : a ≤ b)
    (hρ : ρ * (a + b) = b - a) : ρ ≤ max |1 - ε * a| |1 - ε * b| := by
  by_contra h
  rw [not_le, max_lt_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : 1 - ε * a < ρ := (abs_lt.mp h1).2
  have h2' : -ρ < 1 - ε * b := (abs_lt.mp h2).1
  have hb : 0 < b := by linarith
  have k1 : b * (1 - ε * a) < b * ρ := mul_lt_mul_of_pos_left h1' hb
  have k2 : a * (-ρ) ≤ a * (1 - ε * b) := mul_le_mul_of_nonneg_left h2'.le ha
  nlinarith [k1, k2, hρ]

/-- **Theorem 4.3, case of at least two prime factors.**
If `λ₂ = φ (1 - 1/((p-1)(q-1)))` and `λ_max = φ p/(p-1)`, then
`(λ_max - λ₂) / (λ_max + λ₂) = q / (2 (p-1)(q-1) + q - 2)`. -/
theorem rate_two_primes {φ p q l2 ln : ℝ} (hp : 1 < p) (hq : 1 < q)
    (h2 : l2 * ((p - 1) * (q - 1)) = φ * ((p - 1) * (q - 1) - 1))
    (hn : ln * (p - 1) = φ * p) :
    (ln - l2) * (2 * (p - 1) * (q - 1) + q - 2) = q * (ln + l2) := by
  have hp' : 0 < p - 1 := by linarith
  have hq' : 0 < q - 1 := by linarith
  have huv : (p - 1) * (q - 1) ≠ 0 := (mul_pos hp' hq').ne'
  have key : ((p - 1) * (q - 1)) * ((ln - l2) * (2 * (p - 1) * (q - 1) + q - 2))
      = ((p - 1) * (q - 1)) * (q * (ln + l2)) := by
    linear_combination
      ((q - 1) * (2 * (p - 1) * (q - 1) + q - 2 - q)) * hn
        - (2 * (p - 1) * (q - 1) + q - 2 + q) * h2
  exact mul_left_cancel₀ huv key

/-- **Theorem 4.3, prime-power case.**  If `λ₂ = φ` and `λ_max = φ p/(p-1)`, then
`(λ_max - λ₂) / (λ_max + λ₂) = 1 / (2p - 1)`. -/
theorem rate_prime_power {φ p ln : ℝ} (hp : 1 < p) (hn : ln * (p - 1) = φ * p) :
    (ln - φ) * (2 * p - 1) = ln + φ := by
  have hp' : (p - 1) ≠ 0 := by
    have : 0 < p - 1 := by linarith
    exact this.ne'
  have key : (p - 1) * ((ln - φ) * (2 * p - 1)) = (p - 1) * (ln + φ) := by
    linear_combination (2 * p - 2) * hn
  exact mul_left_cancel₀ hp' key

/-- **Corollary 4.5 (universal bound).**  For `2 ≤ p < q` (so `q ≥ p + 1 ≥ 3`),
`q / (2 (p-1)(q-1) + q - 2) ≤ 3/5`. -/
theorem universal_bound {p q : ℝ} (hp : 2 ≤ p) (hq : 3 ≤ q) :
    5 * q ≤ 3 * (2 * (p - 1) * (q - 1) + q - 2) := by
  have h : 0 ≤ (p - 2) * (q - 3) := mul_nonneg (by linarith) (by linarith)
  nlinarith [h]

/-- **Corollary 4.5 (equality case).**  Equality in the universal bound forces
`(p, q) = (2, 3)`, i.e. `6 ∣ n`. -/
theorem universal_bound_eq {p q : ℝ} (hp : 2 ≤ p) (hq : 3 ≤ q)
    (h : 5 * q = 3 * (2 * (p - 1) * (q - 1) + q - 2)) : p = 2 ∧ q = 3 := by
  have h0 : 0 ≤ (p - 2) * (q - 3) := mul_nonneg (by linarith) (by linarith)
  have e : 6 * ((p - 2) * (q - 3)) + 12 * (p - 2) + 4 * (q - 3) = 0 := by
    linear_combination (-1 : ℝ) * h
  constructor
  · linarith
  · linarith

/-- The denominator `2 (p-1)(q-1) + q - 2` is positive for `p ≥ 2`, `q ≥ 3`. -/
theorem rate_denominator_pos {p q : ℝ} (hp : 2 ≤ p) (hq : 3 ≤ q) :
    0 < 2 * (p - 1) * (q - 1) + q - 2 := by
  have h : 0 ≤ (p - 2) * (q - 3) := mul_nonneg (by linarith) (by linarith)
  nlinarith [h]

end ArithmeticDynamics

/-! ════════════════════════ Part 2: Kuramoto ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part II: the trigonometric core of the Kuramoto results (Section 5 of the paper).
-/

open Real

namespace ArithmeticDynamics

/-- **Lemma 5.2(iii) (Jacobian symbol).**  The contribution of one generator to the
`k`-th Jacobian eigenvalue at a twisted state: with `a = 2π m s / n` and
`b = 2π k s / n`,  `cos a (cos b - 1) = (cos (a+b) + cos (a-b)) / 2 - cos a`.
Summing over the connection set gives `μ_k = (C(m+k) + C(m-k)) / 2 - C(m)`. -/
theorem jacobian_symbol (a b : ℝ) :
    cos a * (cos b - 1) = (cos (a + b) + cos (a - b)) / 2 - cos a := by
  rw [cos_add, cos_sub]
  ring

/-- **Lemma 5.2(i) (twisted states are equilibria), abstract form.**  On a finite
additive group, an even weight against an odd function sums to zero. -/
theorem sum_even_mul_odd_eq_zero {G : Type*} [AddGroup G] [Fintype G]
    (w g : G → ℝ) (hw : ∀ s, w (-s) = w s) (hg : ∀ s, g (-s) = -g s) :
    ∑ s, w s * g s = 0 := by
  have h := Equiv.sum_comp (Equiv.neg G) (fun s => w s * g s)
  simp only [Equiv.neg_apply, hw, hg, mul_neg, Finset.sum_neg_distrib] at h
  linarith

/-- Integers coprime to `6` are of the form `6k ± 1`. -/
theorem coprime_six_form (s : ℤ) (h2 : ¬ (2 : ℤ) ∣ s) (h3 : ¬ (3 : ℤ) ∣ s) :
    ∃ k : ℤ, s = 6 * k + 1 ∨ s = 6 * k - 1 := by
  have h : s % 6 = 1 ∨ s % 6 = 5 := by omega
  rcases h with h | h
  · exact ⟨s / 6, Or.inl (by omega)⟩
  · exact ⟨s / 6 + 1, Or.inr (by omega)⟩

theorem cos_hexagonal_pos (k : ℤ) : cos (π * ((6 * k + 1 : ℤ) : ℝ) / 3) = 1 / 2 := by
  have h : π * ((6 * k + 1 : ℤ) : ℝ) / 3 = π / 3 + (k : ℝ) * (2 * π) := by
    push_cast
    ring
  rw [h, cos_add_int_mul_two_pi, cos_pi_div_three]

theorem cos_hexagonal_neg (k : ℤ) : cos (π * ((6 * k - 1 : ℤ) : ℝ) / 3) = 1 / 2 := by
  have h : π * ((6 * k - 1 : ℤ) : ℝ) / 3 = -(π / 3) + (k : ℝ) * (2 * π) := by
    push_cast
    ring
  rw [h, cos_add_int_mul_two_pi, cos_neg, cos_pi_div_three]

/-- **Theorem 5.5 (hexagonal state), key step.**  If `s` is coprime to `6`, then
the phase lag `π s / 3` across an edge of step `s` has cosine `1/2`; hence the
Jacobian at the hexagonal state equals `-(1/2) L`. -/
theorem cos_hexagonal (s : ℤ) (h2 : ¬ (2 : ℤ) ∣ s) (h3 : ¬ (3 : ℤ) ∣ s) :
    cos (π * (s : ℝ) / 3) = 1 / 2 := by
  obtain ⟨k, hk | hk⟩ := coprime_six_form s h2 h3
  · rw [hk]
    exact cos_hexagonal_pos k
  · rw [hk]
    exact cos_hexagonal_neg k

/-- **Theorem 5.6 (quarter twist), key step.**  If `s` is odd, the phase lag
`π s / 2` has cosine `0`; hence the Jacobian at a quarter twist vanishes. -/
theorem cos_quarter (k : ℤ) : cos (π * ((2 * k + 1 : ℤ) : ℝ) / 2) = 0 := by
  have h : π * ((2 * k + 1 : ℤ) : ℝ) / 2 = (k : ℝ) * π + π / 2 := by
    push_cast
    ring
  rw [h, cos_add_pi_div_two, sin_int_mul_pi, neg_zero]

/-- **Theorem 5.6, energy computation.**  The energy change of the two-vertex
perturbation `(t, -t)` at a quarter twist is `± 2 sin t (1 - cos t)`. -/
theorem quarter_energy (t : ℝ) :
    sin t - sin (-t) + sin (-t - t) = 2 * sin t * (1 - cos t) := by
  have h : -t - t = -(2 * t) := by ring
  rw [h, sin_neg, sin_neg, sin_two_mul]
  ring

/-- The quantity `2 sin t (1 - cos t)` is odd in `t`: the energy takes both signs. -/
theorem quarter_energy_odd (t : ℝ) :
    2 * sin (-t) * (1 - cos (-t)) = -(2 * sin t * (1 - cos t)) := by
  rw [sin_neg, cos_neg]
  ring

/-- **Lemma 5.3, the instability exponent.**  With `x = μ(M)/φ(M)` and
`y = μ(M₂)/φ(M₂)`, the normalised eigenvalue in the direction `k = m` is
`g = (1 + y)/2 - x`.  Three sign computations used in the classification. -/
theorem exponent_odd_order {x : ℝ} (hx : x < 1) : 0 < (1 + x) / 2 - x := by
  linarith

theorem exponent_twice_odd {y : ℝ} (hy : -1 / 3 < y) : 0 < (1 + y) / 2 - (-y) := by
  linarith

theorem exponent_four_dvd {y : ℝ} (hy : -1 < y) : 0 < (1 + y) / 2 - 0 := by
  linarith

end ArithmeticDynamics

/-! ════════════════════════ Part 3: Arithmetic ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part III: totient bounds behind the extremal Ramanujan sums (Section 3 of the paper).
-/

namespace ArithmeticDynamics

/-- If a prime `p` divides `M > 0`, then `p - 1 ≤ φ(M)`. -/
theorem pred_prime_le_totient {p M : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hM : 0 < M) :
    p - 1 ≤ Nat.totient M := by
  have h : Nat.totient p ∣ Nat.totient M := Nat.totient_dvd_of_dvd hpM
  rw [Nat.totient_prime hp] at h
  exact Nat.le_of_dvd (Nat.totient_pos.mpr hM) h

/-- **Lemma 3.1 (i), totient form.**  If `1 < M` and `M ∣ n`, then
`minFac n - 1 ≤ φ(M)`; consequently `-1/φ(M) ≥ -1/(minFac n - 1)`. -/
theorem minFac_pred_le_totient {n M : ℕ} (hM : 1 < M) (hMn : M ∣ n) :
    n.minFac - 1 ≤ Nat.totient M := by
  have hprime : M.minFac.Prime := Nat.minFac_prime (by omega)
  have hdvd : M.minFac ∣ n := dvd_trans (Nat.minFac_dvd M) hMn
  have h1 : n.minFac ≤ M.minFac := Nat.minFac_le_of_dvd hprime.two_le hdvd
  have h2 : M.minFac - 1 ≤ Nat.totient M :=
    pred_prime_le_totient hprime (Nat.minFac_dvd M) (by omega)
  omega

end ArithmeticDynamics

/-! ════════════════════════ Part 4: Extremal ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part IV: the function `r(M) = μ(M)/φ(M)`, its extremal values on the divisors of `n`
(Lemma 3.1 of the paper) and the sign of the instability exponent `g` (Lemma 5.3).
-/

namespace ArithmeticDynamics

open ArithmeticFunction

/-- `r M = μ(M) / φ(M)`; the adjacency eigenvalues of `X_n` are `φ(n) · r(M)`. -/
noncomputable def r (M : ℕ) : ℝ := (moebius M : ℝ) / (Nat.totient M : ℝ)

theorem r_one : r 1 = 1 := by simp [r]

theorem r_prime {p : ℕ} (hp : p.Prime) : r p = -1 / ((p : ℝ) - 1) := by
  simp [r, moebius_apply_prime hp, Nat.totient_prime hp, Nat.cast_sub hp.one_le]

theorem abs_r_le (M : ℕ) : |r M| ≤ 1 / (Nat.totient M : ℝ) := by
  have h : |(moebius M : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := M))
  rw [r, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (Nat.totient M : ℝ) from Nat.cast_nonneg _)]
  gcongr

theorem abs_r_le_half {M : ℕ} (hM : 3 ≤ M) : |r M| ≤ 1 / 2 := by
  have hev : Even (Nat.totient M) := Nat.totient_even (by omega)
  have hpos : 0 < Nat.totient M := Nat.totient_pos.mpr (by omega)
  have h2 : 2 ≤ Nat.totient M := by
    obtain ⟨k, hk⟩ := hev
    omega
  have h2' : (2 : ℝ) ≤ (Nat.totient M : ℝ) := by exact_mod_cast h2
  calc |r M| ≤ 1 / (Nat.totient M : ℝ) := abs_r_le M
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2'

/-- **Lemma 3.1 (i).**  For every divisor `M > 1` of `n`, `r M ≥ -1/(p-1)` with `p = minFac n`. -/
theorem r_ge_of_dvd {n M : ℕ} (hM : 1 < M) (hMn : M ∣ n) :
    -1 / ((n.minFac : ℝ) - 1) ≤ r M := by
  have hn1 : n ≠ 1 := by
    rintro rfl
    have := Nat.le_of_dvd Nat.one_pos hMn
    omega
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have hle : n.minFac - 1 ≤ Nat.totient M := minFac_pred_le_totient hM hMn
  have hle' : (n.minFac : ℝ) - 1 ≤ (Nat.totient M : ℝ) := by
    have : ((n.minFac - 1 : ℕ) : ℝ) ≤ (Nat.totient M : ℝ) := by exact_mod_cast hle
    rwa [Nat.cast_sub hp.one_le, Nat.cast_one] at this
  have hpos : (0 : ℝ) < (n.minFac : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have h1 := abs_r_le M
  have h2 : 1 / (Nat.totient M : ℝ) ≤ 1 / ((n.minFac : ℝ) - 1) :=
    one_div_le_one_div_of_le hpos hle'
  have h3 := neg_abs_le (r M)
  rw [neg_div]
  linarith

/-- **Lemma 3.1 (i), attainment.**  `r(p) = -1/(p-1)` at `p = minFac n`. -/
theorem r_minFac {n : ℕ} (hn : n ≠ 1) : r n.minFac = -1 / ((n.minFac : ℝ) - 1) :=
  r_prime (Nat.minFac_prime hn)

/-- For distinct primes `p`, `q`: `r(pq) = 1/((p-1)(q-1))`. -/
theorem r_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    r (p * q) = 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hμ : moebius (p * q) = 1 := by
    rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp,
      moebius_apply_prime hq]
    norm_num
  rw [r, hμ, Nat.totient_mul hcop, Nat.totient_prime hp, Nat.totient_prime hq]
  push_cast [Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le]
  ring

/-- If `μ(M) = 1` and `M > 1`, then `M` is divisible by two distinct primes. -/
theorem exists_two_primes_of_moebius_eq_one {M : ℕ} (hM : 1 < M) (h : moebius M = 1) :
    ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a ≠ b ∧ a * b ∣ M := by
  have hsq : Squarefree M := moebius_ne_zero_iff_squarefree.mp (by rw [h]; norm_num)
  have hnp : ¬ M.Prime := by
    intro hpr
    rw [moebius_apply_prime hpr] at h
    norm_num at h
  have ha : M.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨m, hm⟩ := Nat.minFac_dvd M
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hnp (hm ▸ ha)
  have hb : m.minFac.Prime := Nat.minFac_prime hm1
  refine ⟨M.minFac, m.minFac, ha, hb, ?_, ?_⟩
  · intro heq
    have hdvd : M.minFac * M.minFac ∣ M := by
      conv_rhs => rw [hm]
      exact Nat.mul_dvd_mul_left _ (heq ▸ Nat.minFac_dvd m)
    have := Nat.isUnit_iff.mp (hsq _ hdvd)
    exact ha.one_lt.ne' this
  · conv_rhs => rw [hm]
    exact Nat.mul_dvd_mul_left _ (Nat.minFac_dvd m)

/-- **Lemma 3.1 (ii).**  Let `p < q` be the two smallest prime divisors of `n`, encoded by
the hypothesis that every prime divisor of `n` is `p` or at least `q`.  Then for every
divisor `M > 1` of `n`, `r M ≤ 1/((p-1)(q-1))`. -/
theorem r_le_of_dvd {n p q M : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hprimes : ∀ l : ℕ, l.Prime → l ∣ n → l = p ∨ q ≤ l) (hM : 1 < M) (hMn : M ∣ n) :
    r M ≤ 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
    linarith
  have hrhs : (0 : ℝ) < 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by positivity
  have hφ : (0 : ℝ) ≤ (Nat.totient M : ℝ) := Nat.cast_nonneg _
  rcases moebius_eq_or M with h | h | h
  · have : r M = 0 := by simp [r, h]
    linarith
  · obtain ⟨a, b, ha, hb, hab, hdvd⟩ := exists_two_primes_of_moebius_eq_one hM h
    have hcop : Nat.Coprime a b := (Nat.coprime_primes ha hb).mpr hab
    have han : a ∣ n := dvd_trans (dvd_trans (Dvd.intro _ rfl) hdvd) hMn
    have hbn : b ∣ n := dvd_trans (dvd_trans (Dvd.intro_left _ rfl) hdvd) hMn
    have hMpos : 0 < M := by omega
    have h1 : (a - 1) * (b - 1) ≤ Nat.totient M := by
      have hd := Nat.totient_dvd_of_dvd hdvd
      rw [Nat.totient_mul hcop, Nat.totient_prime ha, Nat.totient_prime hb] at hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr hMpos) hd
    have h2 : (p - 1) * (q - 1) ≤ (a - 1) * (b - 1) := by
      rcases hprimes a ha han with ha' | ha' <;> rcases hprimes b hb hbn with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · subst ha'
        exact Nat.mul_le_mul_left _ (by omega)
      · subst hb'
        rw [Nat.mul_comm (b - 1) (q - 1)]
        exact Nat.mul_le_mul_right _ (by omega)
      · exact Nat.mul_le_mul (by omega) (by omega)
    have h3 : ((p : ℝ) - 1) * ((q : ℝ) - 1) ≤ (Nat.totient M : ℝ) := by
      have : (((p - 1) * (q - 1) : ℕ) : ℝ) ≤ (Nat.totient M : ℝ) := by
        exact_mod_cast h2.trans h1
      rwa [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le, Nat.cast_one] at this
    have : r M = 1 / (Nat.totient M : ℝ) := by simp [r, h]
    rw [this]
    exact one_div_le_one_div_of_le (mul_pos hp1 hq1) h3
  · have : r M = -1 / (Nat.totient M : ℝ) := by simp [r, h]
    have h0 : (1 : ℝ) / (Nat.totient M : ℝ) ≥ 0 := by positivity
    rw [this, neg_div]
    linarith

/-- **Lemma 3.1 (iii).**  If `n = p^a`, every divisor `M > 1` has `r M ≤ 0`. -/
theorem r_le_zero_of_dvd_prime_pow {p a M : ℕ} (hp : p.Prime) (hM : 1 < M) (h : M ∣ p ^ a) :
    r M ≤ 0 := by
  obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp h
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hM
  rw [r, moebius_apply_prime_pow hp hk]
  have h0 : (1 : ℝ) / (Nat.totient (p ^ k) : ℝ) ≥ 0 := by positivity
  split_ifs
  · push_cast
    rw [neg_div]
    linarith
  · simp

/-- **Lemma 3.1 (iii), attainment.**  `r(p²) = 0`. -/
theorem r_prime_sq {p : ℕ} (hp : p.Prime) : r (p ^ 2) = 0 := by
  rw [r, moebius_apply_prime_pow hp (by norm_num)]
  simp

/-! ### The instability exponent -/

/-- `g M = (1 + r(M / gcd(2, M)))/2 - r M`; the Jacobian at a twisted state of order `M`
has the eigenvalue `K · g M` (Section 5.1 of the paper). -/
noncomputable def g (M : ℕ) : ℝ := (1 + r (M / Nat.gcd 2 M)) / 2 - r M

theorem r_two : r 2 = -1 := by
  rw [r_prime Nat.prime_two]
  norm_num

theorem r_three : r 3 = -1 / 2 := by
  rw [r_prime Nat.prime_three]
  norm_num

theorem r_six : r 6 = 1 / 2 := by
  have h := r_mul_primes Nat.prime_two Nat.prime_three (by norm_num)
  norm_num at h
  exact h

theorem r_eq_zero_of_four_dvd {M : ℕ} (h : 4 ∣ M) : r M = 0 := by
  have hns : ¬ Squarefree M := by
    intro hsq
    have h22 : 2 * 2 ∣ M := by simpa using h
    have := Nat.isUnit_iff.mp (hsq 2 h22)
    norm_num at this
  simp [r, moebius_eq_zero_of_not_squarefree hns]

theorem g_two : g 2 = 2 := by
  have h : 2 / Nat.gcd 2 2 = 1 := by norm_num
  rw [g, h, r_one, r_two]
  norm_num

theorem g_four : g 4 = 0 := by
  have h : 4 / Nat.gcd 2 4 = 2 := by norm_num
  rw [g, h, r_two, r_eq_zero_of_four_dvd (dvd_refl 4)]
  norm_num

theorem g_six : g 6 = -1 / 4 := by
  have h : 6 / Nat.gcd 2 6 = 3 := by norm_num
  rw [g, h, r_three, r_six]
  norm_num

/-- An odd number `M ≥ 5` has `φ(M) ≥ 4`. -/
theorem four_le_totient_of_odd {M : ℕ} (hodd : Odd M) (hM : 5 ≤ M) : 4 ≤ Nat.totient M := by
  have hev : Even (Nat.totient M) := Nat.totient_even (by omega)
  have hpos : 0 < Nat.totient M := Nat.totient_pos.mpr (by omega)
  by_contra hlt
  have h2 : Nat.totient M = 2 := by
    obtain ⟨k, hk⟩ := hev
    omega
  -- every prime divisor `l` of `M` has `l - 1 ≤ 2`, and `l` is odd, hence `l = 3`
  have hl : ∀ l : ℕ, l.Prime → l ∣ M → l = 3 := by
    intro l hlp hlM
    have h1 := pred_prime_le_totient hlp hlM (by omega)
    have hl2 : l ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨c, hc⟩ := hlM
      omega
    have := hlp.two_le
    omega
  have h3 : M.minFac = 3 := hl _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd M)
  obtain ⟨m, hm⟩ := Nat.minFac_dvd M
  rw [h3] at hm
  have hm1 : m ≠ 1 := by
    rintro rfl
    omega
  have hm3 : m.minFac = 3 :=
    hl _ (Nat.minFac_prime hm1) (dvd_trans (Nat.minFac_dvd m) (Dvd.intro_left 3 hm.symm))
  obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
  rw [hm3] at hm'
  have h9 : 9 ∣ M := ⟨m', by rw [hm, hm']; ring⟩
  have h6 : Nat.totient 9 ∣ Nat.totient M := Nat.totient_dvd_of_dvd h9
  have ht9 : Nat.totient 9 = 6 := by decide
  rw [ht9, h2] at h6
  omega

theorem abs_r_le_quarter {M : ℕ} (hodd : Odd M) (hM : 5 ≤ M) : |r M| ≤ 1 / 4 := by
  have h4 : (4 : ℝ) ≤ (Nat.totient M : ℝ) := by exact_mod_cast four_le_totient_of_odd hodd hM
  calc |r M| ≤ 1 / (Nat.totient M : ℝ) := abs_r_le M
    _ ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4

theorem r_two_mul_of_odd {M : ℕ} (hodd : Odd M) : r (2 * M) = - r M := by
  have hcop : Nat.Coprime 2 M := Nat.coprime_two_left.mpr hodd
  rw [r, r, isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime Nat.prime_two,
    Nat.totient_two_mul_of_odd hodd]
  push_cast
  ring

/-- **Lemma 5.3.**  `g M ≥ 1/8` for every `M ≥ 2` other than `4` and `6`. -/
theorem g_ge {M : ℕ} (hM : 2 ≤ M) (h4 : M ≠ 4) (h6 : M ≠ 6) : 1 / 8 ≤ g M := by
  rcases Nat.even_or_odd M with he | ho
  · obtain ⟨N, hN⟩ := he
    have hN2 : M = 2 * N := by omega
    subst hN2
    have hgcd : 2 * N / Nat.gcd 2 (2 * N) = N := by
      have h2 : Nat.gcd 2 (2 * N) = 2 := Nat.gcd_eq_left (Dvd.intro N rfl)
      rw [h2]
      exact Nat.mul_div_cancel_left N (by norm_num)
    rcases Nat.even_or_odd N with he' | ho'
    · -- 4 ∣ M
      have h4dvd : 4 ∣ 2 * N := by
        obtain ⟨k, hk⟩ := he'
        exact ⟨k, by omega⟩
      have hN3 : 3 ≤ N := by
        obtain ⟨k, hk⟩ := he'
        omega
      have := abs_le.mp (abs_r_le_half hN3)
      rw [g, hgcd, r_eq_zero_of_four_dvd h4dvd]
      linarith [this.1]
    · rw [g, hgcd, r_two_mul_of_odd ho']
      by_cases hN1 : N = 1
      · subst hN1
        rw [r_one]
        norm_num
      · have hN5 : 5 ≤ N := by
          obtain ⟨k, hk⟩ := ho'
          omega
        have := abs_le.mp (abs_r_le_quarter ho' hN5)
        linarith [this.1]
  · have hcop : Nat.gcd 2 M = 1 := Nat.coprime_two_left.mpr ho
    have hM3 : 3 ≤ M := by
      obtain ⟨k, hk⟩ := ho
      omega
    have := abs_le.mp (abs_r_le_half hM3)
    rw [g, hcop, Nat.div_one]
    linarith [this.2]

end ArithmeticDynamics

/-! ════════════════════════ Part 5: Ramanujan ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part V: Ramanujan sums and Hölder's formula  `c_n(j) = φ(n) · μ(M)/φ(M)`,  `M = ord(j)`
(equation (2.3) of the paper), proved from scratch.
-/

namespace ArithmeticDynamics

open ArithmeticFunction Finset

/-- Möbius indicator of coprimality: `∑_{d ∣ M, d ∣ k} μ(d) = [gcd(k, M) = 1]`. -/
theorem sum_moebius_filter_dvd (k : ℕ) {M : ℕ} (hM : M ≠ 0) :
    ∑ d ∈ (Nat.divisors M).filter (fun d => d ∣ k), (moebius d : ℤ)
      = if Nat.Coprime k M then 1 else 0 := by
  have hset : (Nat.divisors M).filter (fun d => d ∣ k) = Nat.divisors (Nat.gcd k M) := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, ne_eq, Nat.gcd_eq_zero_iff]
    tauto
  rw [hset, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- Reindexing the multiples of `d` below `d * e`. -/
theorem sum_filter_dvd_range {d e : ℕ} (hd : 0 < d) (f : ℕ → ℂ) :
    ∑ k ∈ (range (d * e)).filter (fun k => d ∣ k), f k = ∑ t ∈ range e, f (d * t) := by
  have himg : (range (d * e)).filter (fun k => d ∣ k) = (range e).image (fun t => d * t) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hk, t, rfl⟩
      exact ⟨t, Nat.lt_of_mul_lt_mul_left hk, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left ht hd, Dvd.intro t rfl⟩
  rw [himg, sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hd hab

/-- Sum of the powers of a primitive `M`-th root of unity over the multiples of `d ∣ M`. -/
theorem sum_filter_dvd_pow {M d : ℕ} (hM : 0 < M) (hd : d ∣ M) {ξ : ℂ}
    (hξ : IsPrimitiveRoot ξ M) :
    ∑ k ∈ (range M).filter (fun k => d ∣ k), ξ ^ k = if d = M then 1 else 0 := by
  obtain ⟨e, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
  have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
  rw [sum_filter_dvd_range hd0]
  have hprim : IsPrimitiveRoot (ξ ^ d) e := hξ.pow hM rfl
  simp_rw [pow_mul]
  by_cases he : e = 1
  · subst he
    simp
  · have he1 : 1 < e := by omega
    rw [hprim.geom_sum_eq_zero he1]
    have : d ≠ d * e := by
      intro h
      have : d * 1 = d * e := by simpa using h
      exact he (Nat.eq_of_mul_eq_mul_left hd0 this).symm
    simp [this]

/-- **Ramanujan's sum at a primitive root.**  The sum of `ξ^k` over the reduced residues
`k` modulo `M` equals `μ(M)` for every primitive `M`-th root of unity `ξ`. -/
theorem sum_coprime_pow_primitiveRoot {M : ℕ} (hM : 0 < M) {ξ : ℂ}
    (hξ : IsPrimitiveRoot ξ M) :
    ∑ k ∈ (range M).filter (fun k => Nat.Coprime k M), ξ ^ k = (moebius M : ℂ) := by
  have hM0 : M ≠ 0 := hM.ne'
  have hind : ∀ k : ℕ, (if Nat.Coprime k M then (1 : ℂ) else 0)
      = ∑ d ∈ (Nat.divisors M).filter (fun d => d ∣ k), (moebius d : ℂ) := by
    intro k
    have h := sum_moebius_filter_dvd k hM0
    have h' := congrArg (fun z : ℤ => (z : ℂ)) h
    simp only [Int.cast_sum] at h'
    rw [h']
    split_ifs <;> simp
  calc ∑ k ∈ (range M).filter (fun k => Nat.Coprime k M), ξ ^ k
      = ∑ k ∈ range M, (if Nat.Coprime k M then (1 : ℂ) else 0) * ξ ^ k := by
        rw [sum_filter]
        refine sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
    _ = ∑ k ∈ range M, ∑ d ∈ Nat.divisors M,
          (if d ∣ k then (moebius d : ℂ) * ξ ^ k else 0) := by
        refine sum_congr rfl fun k _ => ?_
        rw [hind k, sum_mul, sum_filter]
    _ = ∑ d ∈ Nat.divisors M, ∑ k ∈ range M,
          (if d ∣ k then (moebius d : ℂ) * ξ ^ k else 0) := sum_comm
    _ = ∑ d ∈ Nat.divisors M, (moebius d : ℂ) * (if d = M then 1 else 0) := by
        refine sum_congr rfl fun d hd => ?_
        rw [← sum_filter_dvd_pow hM (Nat.dvd_of_mem_divisors hd) hξ, mul_sum, sum_filter]
    _ = (moebius M : ℂ) := by
        simp [hM0]

/-- Sums over the unit group of `ZMod M` are sums over reduced residues. -/
theorem sum_units_val (M : ℕ) [NeZero M] (f : ℕ → ℂ) :
    ∑ v : (ZMod M)ˣ, f (v : ZMod M).val
      = ∑ k ∈ (range M).filter (fun k => Nat.Coprime k M), f k := by
  refine sum_bij (fun v _ => (v : ZMod M).val) ?_ ?_ ?_ ?_
  · intro v _
    exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime v⟩
  · intro a _ b _ hab
    exact Units.ext (ZMod.val_injective M hab)
  · intro k hk
    obtain ⟨hk1, hk2⟩ := mem_filter.mp hk
    refine ⟨ZMod.unitOfCoprime k hk2, mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt (mem_range.mp hk1)]
  · intro v _
    rfl

/-- Fibre counting for the reduction map `(ℤ/n)ˣ → (ℤ/M)ˣ`, `M ∣ n`. -/
theorem totient_mul_sum_unitsMap {n M : ℕ} [NeZero n] [NeZero M] (h : M ∣ n)
    (F : (ZMod M)ˣ → ℂ) :
    (Nat.totient M : ℂ) * ∑ u : (ZMod n)ˣ, F (ZMod.unitsMap h u)
      = (Nat.totient n : ℂ) * ∑ v : (ZMod M)ˣ, F v := by
  classical
  set f := ZMod.unitsMap h with hf
  have hsurj : Function.Surjective f := ZMod.unitsMap_surjective h
  set c : ℕ := #{u : (ZMod n)ˣ | f u = 1} with hc
  have hfib : ∀ v : (ZMod M)ˣ, #{u : (ZMod n)ˣ | f u = v} = c := fun v =>
    MonoidHom.card_fiber_eq_of_mem_range f (hsurj v) (hsurj 1)
  have hsum : ∀ G : (ZMod M)ˣ → ℂ, ∑ u : (ZMod n)ˣ, G (f u) = (c : ℂ) * ∑ v, G v := by
    intro G
    rw [← Finset.sum_fiberwise' (univ : Finset (ZMod n)ˣ) f G, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [sum_const, hfib v, nsmul_eq_mul]
  have hcard : (Nat.totient n : ℂ) = (c : ℂ) * (Nat.totient M : ℂ) := by
    have h1 := hsum (fun _ => 1)
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h1
    rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at h1
    exact h1
  rw [hsum F, hcard]
  ring

/-- The Ramanujan sum `c_n(j) = ∑_{u ∈ (ℤ/n)ˣ} e(j u / n)`: the adjacency eigenvalue of the
unitary Cayley graph `X_n` attached to the character `χ_j`. -/
noncomputable def ramanujan (n : ℕ) [NeZero n] (j : ZMod n) : ℂ :=
  ∑ u : (ZMod n)ˣ, ZMod.stdAddChar (j * (u : ZMod n))

theorem pow_mod_of_pow_eq_one {ξ : ℂ} {M : ℕ} (h : ξ ^ M = 1) (a : ℕ) :
    ξ ^ (a % M) = ξ ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a M, pow_add, pow_mul, h, one_pow, mul_one]

/-- `e(j/n)` is a primitive root of unity of order `ord(j)`. -/
theorem isPrimitiveRoot_stdAddChar {n : ℕ} [NeZero n] (j : ZMod n) :
    IsPrimitiveRoot (ZMod.stdAddChar j : ℂ) (addOrderOf j) := by
  have key : ∀ l : ℕ, (ZMod.stdAddChar j : ℂ) ^ l = 1 ↔ addOrderOf j ∣ l := by
    intro l
    rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := n)),
      (ZMod.injective_stdAddChar (N := n)).eq_iff, addOrderOf_dvd_iff_nsmul_eq_zero]
  exact ⟨(key _).mpr dvd_rfl, fun l hl => (key l).mp hl⟩

theorem stdAddChar_mul_eq_pow {n : ℕ} [NeZero n] (j x : ZMod n) :
    (ZMod.stdAddChar (j * x) : ℂ) = (ZMod.stdAddChar j : ℂ) ^ x.val := by
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

/-- **Hölder's formula.**  `c_n(j) = φ(n) · μ(M)/φ(M)` with `M = ord(j)`. -/
theorem ramanujan_eq {n : ℕ} [NeZero n] (j : ZMod n) :
    ramanujan n j = (Nat.totient n : ℂ) * ((r (addOrderOf j) : ℝ) : ℂ) := by
  set M := addOrderOf j with hMdef
  have hMpos : 0 < M := addOrderOf_pos j
  have : NeZero M := ⟨hMpos.ne'⟩
  have hMn : M ∣ n := by
    have := addOrderOf_dvd_card (x := j)
    rwa [ZMod.card] at this
  set ξ : ℂ := ZMod.stdAddChar j with hξdef
  have hξ : IsPrimitiveRoot ξ M := isPrimitiveRoot_stdAddChar j
  have h1 : ramanujan n j = ∑ u : (ZMod n)ˣ, ξ ^ ((ZMod.unitsMap hMn u : (ZMod M)ˣ) : ZMod M).val := by
    unfold ramanujan
    refine sum_congr rfl fun u _ => ?_
    rw [stdAddChar_mul_eq_pow, ZMod.unitsMap_val, ← ZMod.natCast_val, ZMod.val_natCast,
      pow_mod_of_pow_eq_one hξ.pow_eq_one]
  have h2 := totient_mul_sum_unitsMap hMn (fun v : (ZMod M)ˣ => ξ ^ (v : ZMod M).val)
  rw [← h1, sum_units_val M (fun k => ξ ^ k), sum_coprime_pow_primitiveRoot hMpos hξ] at h2
  have hφ : (Nat.totient M : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hMpos).ne'
  rw [r]
  push_cast
  field_simp
  linear_combination h2

end ArithmeticDynamics

/-! ════════════════════════ Part 6: Spectrum ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part VI: the spectrum of the unitary Cayley graph `X_n` (Theorem 3.2) and the exact
consensus rate (Theorem 4.3).
-/

namespace ArithmeticDynamics

open Finset

variable (n : ℕ) [NeZero n]

/-- The unitary Cayley graph `X_n`: `a ∼ b` iff `a ≠ b` and `b - a` is a unit of `ℤ/n`. -/
def unitaryCayley : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (fun a b => IsUnit (b - a))

omit [NeZero n] in
theorem unitaryCayley_adj (a b : ZMod n) :
    (unitaryCayley n).Adj a b ↔ a ≠ b ∧ IsUnit (b - a) := by
  unfold unitaryCayley
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hab, h | h⟩
    · exact ⟨hab, h⟩
    · refine ⟨hab, ?_⟩
      have : b - a = -(a - b) := by ring
      rw [this]
      exact h.neg
  · rintro ⟨hab, h⟩
    exact ⟨hab, Or.inl h⟩

/-- The adjacency operator of `X_n` acting on functions `ℤ/n → ℂ`. -/
noncomputable def adj (f : ZMod n → ℂ) (i : ZMod n) : ℂ := ∑ u : (ZMod n)ˣ, f (i + u)

/-- The Laplacian operator `L = φ(n) I - A` of `X_n`. -/
noncomputable def lap (f : ZMod n → ℂ) (i : ZMod n) : ℂ :=
  (Nat.totient n : ℂ) * f i - adj n f i

open Classical in
/-- `adj` is the adjacency operator of the simple graph `X_n` (for `n ≥ 2`). -/
theorem adj_eq_sum_neighbors (hn : 1 < n) (f : ZMod n → ℂ) (i : ZMod n) :
    adj n f i = ∑ j ∈ univ.filter (fun j => (unitaryCayley n).Adj i j), f j := by
  have : Fact (1 < n) := ⟨hn⟩
  unfold adj
  refine sum_bij (fun u _ => i + (u : ZMod n)) ?_ ?_ ?_ ?_
  · intro u _
    refine mem_filter.mpr ⟨mem_univ _, (unitaryCayley_adj n _ _).mpr ⟨?_, ?_⟩⟩
    · intro h
      have : (u : ZMod n) = 0 := by
        have h' : i + (u : ZMod n) = i + 0 := by rw [add_zero]; exact h.symm
        exact add_left_cancel h'
      exact u.ne_zero this
    · have : i + (u : ZMod n) - i = u := by ring
      rw [this]
      exact u.isUnit
  · intro a _ b _ hab
    exact Units.ext (add_left_cancel hab)
  · intro j hj
    obtain ⟨_, hu⟩ := (unitaryCayley_adj n _ _).mp (mem_filter.mp hj).2
    refine ⟨hu.unit, mem_univ _, ?_⟩
    rw [IsUnit.unit_spec]
    ring
  · intro u _
    rfl

/-- The character `χ_k(x) = e(kx/n)`. -/
noncomputable def chi (k : ZMod n) : ZMod n → ℂ := fun x => ZMod.stdAddChar (k * x)

/-- Characters are eigenvectors of the adjacency operator, with eigenvalue the Ramanujan sum. -/
theorem adj_chi (k i : ZMod n) : adj n (chi n k) i = ramanujan n k * chi n k i := by
  unfold adj chi ramanujan
  rw [sum_mul]
  refine sum_congr rfl fun u _ => ?_
  rw [mul_add, AddChar.map_add_eq_mul, mul_comm]

/-- The Laplacian eigenvalue of `X_n` attached to `χ_k`:  `λ(k) = φ(n) (1 - r(ord k))`. -/
noncomputable def lapEig (k : ZMod n) : ℝ := (Nat.totient n : ℝ) * (1 - r (addOrderOf k))

/-- **Spectrum of `X_n`** (equation (2.4)): `L χ_k = φ(n)(1 - μ(M)/φ(M)) χ_k`, `M = ord k`. -/
theorem lap_chi (k i : ZMod n) : lap n (chi n k) i = ((lapEig n k : ℝ) : ℂ) * chi n k i := by
  unfold lap lapEig
  rw [adj_chi, ramanujan_eq]
  push_cast
  ring

variable {n}

theorem one_lt_addOrderOf {k : ZMod n} (hk : k ≠ 0) : 1 < addOrderOf k := by
  have h1 : addOrderOf k ≠ 1 := fun h => hk (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have h0 : 0 < addOrderOf k := addOrderOf_pos k
  omega

theorem addOrderOf_dvd_self (k : ZMod n) : addOrderOf k ∣ n := by
  have := addOrderOf_dvd_card (x := k)
  rwa [ZMod.card] at this

/-- For `M ∣ n`, the residue `n / M` has additive order `M`. -/
theorem addOrderOf_natCast_div {M : ℕ} (hM : M ∣ n) :
    addOrderOf ((n / M : ℕ) : ZMod n) = M := by
  have hn0 : n ≠ 0 := NeZero.ne n
  rw [ZMod.addOrderOf_coe _ hn0, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hM),
    Nat.div_div_self hM hn0]

theorem natCast_div_ne_zero {M : ℕ} (hM : M ∣ n) (h1 : 1 < M) : ((n / M : ℕ) : ZMod n) ≠ 0 := by
  intro h
  have := addOrderOf_natCast_div (n := n) hM
  rw [h, addOrderOf_zero] at this
  omega

/-! ### Theorem 3.2: the extreme Laplacian eigenvalues -/

/-- **Theorem 3.2, upper bound.**  Every eigenvalue is at most `φ(n) p/(p-1)`, `p = minFac n`. -/
theorem lapEig_le (k : ZMod n) (hk : k ≠ 0) :
    lapEig n k ≤ (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1)) := by
  have h := r_ge_of_dvd (one_lt_addOrderOf hk) (addOrderOf_dvd_self k)
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hk (Subsingleton.elim _ _)
  have hp : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast (Nat.minFac_prime hn1).two_le
  have hp1 : (0 : ℝ) < (n.minFac : ℝ) - 1 := by linarith
  have hφ : (0 : ℝ) ≤ (Nat.totient n : ℝ) := Nat.cast_nonneg _
  have e : (n.minFac : ℝ) / ((n.minFac : ℝ) - 1) = 1 - (-1 / ((n.minFac : ℝ) - 1)) := by
    field_simp
    ring
  unfold lapEig
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) hφ

/-- **Theorem 3.2, `λ_max` is attained** at the residue `n / p`. -/
theorem lapEig_minFac (hn : 1 < n) :
    lapEig n ((n / n.minFac : ℕ) : ZMod n)
      = (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1)) := by
  have hn1 : n ≠ 1 := by omega
  have hp : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast (Nat.minFac_prime hn1).two_le
  have hp1 : (n.minFac : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (n.minFac : ℝ) - 1 := by linarith
    exact this.ne'
  unfold lapEig
  rw [addOrderOf_natCast_div (Nat.minFac_dvd n), r_minFac hn1]
  field_simp
  ring

/-- **Theorem 3.2, lower bound when `ω(n) ≥ 2`.**  Here `p < q` are the two smallest prime
divisors of `n`. -/
theorem lapEig_ge_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hprimes : ∀ l : ℕ, l.Prime → l ∣ n → l = p ∨ q ≤ l) (k : ZMod n) (hk : k ≠ 0) :
    (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1))) ≤ lapEig n k := by
  have h := r_le_of_dvd hp hq hpq hprimes (one_lt_addOrderOf hk) (addOrderOf_dvd_self k)
  have hφ : (0 : ℝ) ≤ (Nat.totient n : ℝ) := Nat.cast_nonneg _
  unfold lapEig
  exact mul_le_mul_of_nonneg_left (by linarith) hφ

/-- **Theorem 3.2, `λ₂` is attained** at the residue `n / (pq)` when `pq ∣ n`. -/
theorem lapEig_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hdvd : p * q ∣ n) :
    lapEig n ((n / (p * q) : ℕ) : ZMod n)
      = (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1))) := by
  unfold lapEig
  rw [addOrderOf_natCast_div hdvd, r_mul_primes hp hq hpq]

/-- **Theorem 3.2, lower bound for prime powers.** -/
theorem lapEig_ge_prime_pow {p a : ℕ} (hp : p.Prime) (hn : n = p ^ a) (k : ZMod n) (hk : k ≠ 0) :
    (Nat.totient n : ℝ) ≤ lapEig n k := by
  have hd : addOrderOf k ∣ p ^ a := hn ▸ addOrderOf_dvd_self k
  have h := r_le_zero_of_dvd_prime_pow hp (one_lt_addOrderOf hk) hd
  have hφ : (0 : ℝ) ≤ (Nat.totient n : ℝ) := Nat.cast_nonneg _
  unfold lapEig
  nlinarith [mul_nonneg hφ (neg_nonneg.mpr h)]

/-- **Theorem 3.2, `λ₂ = φ(n)` is attained for `n = p^a`, `a ≥ 2`,** at the residue `n / p²`. -/
theorem lapEig_prime_sq {p : ℕ} (hp : p.Prime) (hdvd : p ^ 2 ∣ n) :
    lapEig n ((n / p ^ 2 : ℕ) : ZMod n) = (Nat.totient n : ℝ) := by
  unfold lapEig
  rw [addOrderOf_natCast_div hdvd, r_prime_sq hp]
  ring

/-! ### Theorem 4.3: the exact consensus rate on `X_n` -/

omit [NeZero n] in
/-- **Theorem 4.3 for `X_n`, `ω(n) ≥ 2`.**  With `λ₂` and `λ_max` the extreme Laplacian
eigenvalues from Theorem 3.2, the optimal rate `(λ_max - λ₂)/(λ_max + λ₂)` equals
`q / (2(p-1)(q-1) + q - 2)`. -/
theorem consensus_rate_unitaryCayley {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpn : n.minFac = p) :
    let l2 := (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)))
    let lmax := (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1))
    (lmax - l2) * (2 * ((p : ℝ) - 1) * ((q : ℝ) - 1) + (q : ℝ) - 2) = (q : ℝ) * (lmax + l2) := by
  intro l2 lmax
  have hp2 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hq2 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    exact this.ne'
  have hq1 : (q : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) - 1 := by linarith
    exact this.ne'
  refine rate_two_primes (φ := (Nat.totient n : ℝ)) hp2 hq2 ?_ ?_
  · simp only [l2]
    field_simp
  · simp only [lmax, hpn]
    field_simp

end ArithmeticDynamics

/-! ════════════════════════ Part 7: Twisted ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part VII: twisted states of the Kuramoto model on `X_n` (Section 5 of the paper):
equilibria, the Jacobian and its spectrum, and the classification by additive order.
-/

namespace ArithmeticDynamics

open Finset Real

variable (n : ℕ) [NeZero n]

/-! ### Real and imaginary parts of the standard character -/

theorem stdAddChar_natCast (a : ℕ) :
    (ZMod.stdAddChar ((a : ℕ) : ZMod n) : ℂ)
      = Complex.exp (((2 * π * a / n : ℝ) : ℂ) * Complex.I) := by
  have h := ZMod.stdAddChar_coe (N := n) (a : ℤ)
  simp only [Int.cast_natCast] at h
  rw [h]
  congr 1
  push_cast
  ring

theorem stdAddChar_natCast_re (a : ℕ) :
    (ZMod.stdAddChar ((a : ℕ) : ZMod n) : ℂ).re = cos (2 * π * a / n) := by
  rw [stdAddChar_natCast, Complex.exp_ofReal_mul_I_re]

theorem stdAddChar_natCast_im (a : ℕ) :
    (ZMod.stdAddChar ((a : ℕ) : ZMod n) : ℂ).im = sin (2 * π * a / n) := by
  rw [stdAddChar_natCast, Complex.exp_ofReal_mul_I_im]

/-! ### The Kuramoto vector field and the twisted states -/

/-- The Kuramoto vector field on `X_n` (in the co-rotating frame):
`F(θ)_i = (K/φ(n)) ∑_u sin(θ_{i+u} - θ_i)`. -/
noncomputable def kuramotoField (K : ℝ) (θ : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  K / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, sin (θ (i + u) - θ i)

/-- The `a`-twisted state `θ_j = 2π a j / n`. -/
noncomputable def twisted (a : ℕ) : ZMod n → ℝ := fun x => 2 * π * a * x.val / n

/-- The edge weight `cos(2π m u / n)` at the `m`-twisted state. -/
noncomputable def twistWeight (m : ZMod n) (u : (ZMod n)ˣ) : ℝ :=
  (ZMod.stdAddChar (m * (u : ZMod n)) : ℂ).re

theorem natCast_mul_unit (a : ℕ) (u : (ZMod n)ˣ) :
    ((a : ℕ) : ZMod n) * (u : ZMod n) = ((a * (u : ZMod n).val : ℕ) : ZMod n) := by
  push_cast
  rw [ZMod.natCast_zmod_val]

theorem twistWeight_natCast (a : ℕ) (u : (ZMod n)ˣ) :
    twistWeight n (a : ZMod n) u = cos (2 * π * (a * (u : ZMod n).val : ℕ) / n) := by
  unfold twistWeight
  rw [natCast_mul_unit, stdAddChar_natCast_re]

/-- Phase differences along an edge at a twisted state, modulo `2π`. -/
theorem twisted_diff (a : ℕ) (i : ZMod n) (u : (ZMod n)ˣ) :
    twisted n a (i + u) - twisted n a i
      = 2 * π * (a * (u : ZMod n).val : ℕ) / n
        - ((a * ((i.val + (u : ZMod n).val) / n) : ℕ) : ℤ) * (2 * π) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hval : (((i + (u : ZMod n)).val : ℕ) : ℝ)
      = (i.val : ℝ) + ((u : ZMod n).val : ℝ) - (n : ℝ) * (((i.val + (u : ZMod n).val) / n : ℕ) : ℝ) := by
    have h := Nat.mod_add_div (i.val + (u : ZMod n).val) n
    rw [← ZMod.val_add] at h
    have h' : (((i + (u : ZMod n)).val + n * ((i.val + (u : ZMod n).val) / n) : ℕ) : ℝ)
        = ((i.val + (u : ZMod n).val : ℕ) : ℝ) := by exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) h
    push_cast at h'
    linarith
  unfold twisted
  rw [hval, Int.cast_natCast]
  push_cast
  field_simp
  ring

theorem cos_twisted_diff (a : ℕ) (i : ZMod n) (u : (ZMod n)ˣ) :
    cos (twisted n a (i + u) - twisted n a i) = twistWeight n (a : ZMod n) u := by
  rw [twisted_diff, cos_sub_int_mul_two_pi, twistWeight_natCast]

theorem sin_twisted_diff (a : ℕ) (i : ZMod n) (u : (ZMod n)ˣ) :
    sin (twisted n a (i + u) - twisted n a i)
      = (ZMod.stdAddChar ((a : ZMod n) * (u : ZMod n)) : ℂ).im := by
  rw [twisted_diff, sin_sub_int_mul_two_pi, natCast_mul_unit, stdAddChar_natCast_im]

/-- **Lemma 5.2 (i).**  Every twisted state is an equilibrium of the Kuramoto model on `X_n`. -/
theorem kuramotoField_twisted (K : ℝ) (a : ℕ) (i : ZMod n) :
    kuramotoField n K (twisted n a) i = 0 := by
  unfold kuramotoField
  have h : ∑ u : (ZMod n)ˣ, sin (twisted n a (i + u) - twisted n a i)
      = (ramanujan n (a : ZMod n)).im := by
    unfold ramanujan
    rw [Complex.im_sum]
    exact sum_congr rfl fun u _ => sin_twisted_diff n a i u
  rw [h, ramanujan_eq]
  have : ((Nat.totient n : ℂ) * ((r (addOrderOf ((a : ℕ) : ZMod n)) : ℝ) : ℂ)).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_im]
  rw [this, mul_zero]

/-- **Lemma 5.2 (ii).**  The derivative of the Kuramoto vector field at `θ` in the direction
`f` is `(K/φ(n)) ∑_u cos(θ_{i+u} - θ_i) (f_{i+u} - f_i)`. -/
theorem hasDerivAt_kuramotoField (K : ℝ) (θ f : ZMod n → ℝ) (i : ZMod n) :
    HasDerivAt (fun t : ℝ => kuramotoField n K (fun x => θ x + t * f x) i)
      (K / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, cos (θ (i + u) - θ i) * (f (i + u) - f i)) 0 := by
  unfold kuramotoField
  refine HasDerivAt.const_mul _ ?_
  refine HasDerivAt.fun_sum fun u _ => ?_
  have h1 : HasDerivAt (fun t : ℝ => θ (i + u) + t * f (i + u) - (θ i + t * f i))
      (f (i + u) - f i) 0 := by
    have ha : HasDerivAt (fun t : ℝ => θ (i + u) + t * f (i + u)) (f (i + u)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (f (i + u))).const_add (θ (i + u))
    have hb : HasDerivAt (fun t : ℝ => θ i + t * f i) (f i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (f i)).const_add (θ i)
    exact ha.sub hb
  have h2 := h1.sin
  simpa using h2

/-! ### The Jacobian at a twisted state and its spectrum -/

/-- The Jacobian of the Kuramoto model on `X_n` at the `m`-twisted state, acting on
functions `ℤ/n → ℂ`:  `(J f)_i = (K/φ(n)) ∑_u cos(2π m u/n) (f_{i+u} - f_i)`. -/
noncomputable def jac (K : ℝ) (m : ZMod n) (f : ZMod n → ℂ) (i : ZMod n) : ℂ :=
  ((K / (Nat.totient n : ℝ) : ℝ) : ℂ) * ∑ u : (ZMod n)ˣ, (twistWeight n m u : ℂ) * (f (i + u) - f i)

/-- The operator `jac` is the linearisation of the Kuramoto field at the twisted state. -/
theorem hasDerivAt_kuramotoField_twisted (K : ℝ) (a : ℕ) (f : ZMod n → ℝ) (i : ZMod n) :
    HasDerivAt (fun t : ℝ => kuramotoField n K (fun x => twisted n a x + t * f x) i)
      (K / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, twistWeight n (a : ZMod n) u * (f (i + u) - f i)) 0 := by
  have h := hasDerivAt_kuramotoField n K (twisted n a) f i
  simp only [cos_twisted_diff] at h
  exact h

theorem jac_ofReal (K : ℝ) (m : ZMod n) (f : ZMod n → ℝ) (i : ZMod n) :
    jac n K m (fun x => (f x : ℂ)) i
      = ((K / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, twistWeight n m u * (f (i + u) - f i) : ℝ) : ℂ) := by
  unfold jac
  push_cast
  rfl

theorem twistWeight_eq (m : ZMod n) (u : (ZMod n)ˣ) :
    (twistWeight n m u : ℂ)
      = ((ZMod.stdAddChar (m * (u : ZMod n)) : ℂ) + ZMod.stdAddChar (-(m * (u : ZMod n)))) / 2 := by
  unfold twistWeight
  rw [Complex.re_eq_add_conj, AddChar.map_neg_eq_conj]

/-- **Lemma 5.2 (iii), in terms of Ramanujan sums.** -/
theorem jac_chi_ramanujan (K : ℝ) (m k i : ZMod n) :
    jac n K m (chi n k) i
      = ((K / (Nat.totient n : ℝ) : ℝ) : ℂ)
          * ((ramanujan n (m + k) + ramanujan n (k - m)) / 2
              - (ramanujan n m + ramanujan n (-m)) / 2) * chi n k i := by
  have hterm : ∀ u : (ZMod n)ˣ, (twistWeight n m u : ℂ) * (chi n k (i + u) - chi n k i)
      = ((ZMod.stdAddChar ((m + k) * (u : ZMod n)) + ZMod.stdAddChar ((k - m) * (u : ZMod n))) / 2
          - (ZMod.stdAddChar (m * (u : ZMod n)) + ZMod.stdAddChar (-m * (u : ZMod n))) / 2)
        * chi n k i := by
    intro u
    have e1 : (m + k) * (u : ZMod n) = m * u + k * u := by ring
    have e2 : (k - m) * (u : ZMod n) = k * u + -(m * u) := by ring
    have e3 : -m * (u : ZMod n) = -(m * u) := by ring
    have e4 : k * (i + (u : ZMod n)) = k * i + k * u := by ring
    rw [twistWeight_eq]
    unfold chi
    rw [e1, e2, e3, e4, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring
  unfold jac
  rw [mul_assoc]
  congr 1
  rw [sum_congr rfl fun u _ => hterm u, ← sum_mul]
  congr 1
  simp only [ramanujan, add_div, sum_sub_distrib, sum_add_distrib, sum_div]

/-- **Lemma 5.2 (iii).**  `J χ_k = K · μ_k/φ(n) · χ_k` with
`μ_k/φ(n) = (r(ord(m+k)) + r(ord(m-k)))/2 - r(ord m)`  (equation (5.5)). -/
theorem jac_chi (K : ℝ) (m k i : ZMod n) :
    jac n K m (chi n k) i
      = ((K * ((r (addOrderOf (m + k)) + r (addOrderOf (m - k))) / 2 - r (addOrderOf m)) : ℝ) : ℂ)
          * chi n k i := by
  have hφ : (Nat.totient n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  have hsub : addOrderOf (k - m) = addOrderOf (m - k) := by
    rw [← addOrderOf_neg, neg_sub]
  rw [jac_chi_ramanujan, ramanujan_eq, ramanujan_eq, ramanujan_eq, ramanujan_eq, addOrderOf_neg,
    hsub]
  push_cast
  field_simp
  ring

variable {n}

/-- **Theorem 5.4 (c), eigenvalue.**  In the direction `χ_m`, the Jacobian at the
`m`-twisted state has the eigenvalue `K · g(ord m)`. -/
theorem jac_chi_self (K : ℝ) (m i : ZMod n) :
    jac n K m (chi n m) i = ((K * g (addOrderOf m) : ℝ) : ℂ) * chi n m i := by
  have h2 : addOrderOf (m + m) = addOrderOf m / Nat.gcd 2 (addOrderOf m) := by
    rw [← two_nsmul, addOrderOf_nsmul, Nat.gcd_comm]
  rw [jac_chi, h2, sub_self, addOrderOf_zero, r_one]
  unfold g
  congr 2
  ring

/-- **Theorem 5.4 (c).**  If `m ≠ 0` and `ord m ∉ {4, 6}`, the eigenvalue `K · g(ord m)` in
the direction `χ_m` is at least `K/8 > 0`: the twisted state is linearly unstable. -/
theorem twisted_unstable {K : ℝ} (hK : 0 < K) {m : ZMod n} (hm : m ≠ 0)
    (h4 : addOrderOf m ≠ 4) (h6 : addOrderOf m ≠ 6) :
    K / 8 ≤ K * g (addOrderOf m) ∧ 0 < K * g (addOrderOf m) := by
  have h := g_ge (one_lt_addOrderOf hm) h4 h6
  constructor <;> nlinarith

/-! ### Hexagonal states (Theorem 5.5) -/

omit [NeZero n] in
theorem not_two_dvd_unit_val (h2 : 2 ∣ n) (u : (ZMod n)ˣ) : ¬ (2 : ℤ) ∣ ((u : ZMod n).val : ℤ) := by
  intro h
  have h' : 2 ∣ (u : ZMod n).val := by exact_mod_cast h
  have hc := ZMod.val_coe_unit_coprime u
  have := Nat.dvd_gcd h' h2
  rw [hc] at this
  omega

omit [NeZero n] in
theorem not_three_dvd_unit_val (h3 : 3 ∣ n) (u : (ZMod n)ˣ) :
    ¬ (3 : ℤ) ∣ ((u : ZMod n).val : ℤ) := by
  intro h
  have h' : 3 ∣ (u : ZMod n).val := by exact_mod_cast h
  have hc := ZMod.val_coe_unit_coprime u
  have := Nat.dvd_gcd h' h3
  rw [hc] at this
  omega

/-- At the hexagonal state `m = n/6` every edge weight is `cos(π/3) = 1/2`. -/
theorem twistWeight_hex (h6 : 6 ∣ n) (u : (ZMod n)ˣ) :
    twistWeight n ((n / 6 : ℕ) : ZMod n) u = 1 / 2 := by
  obtain ⟨t, ht⟩ := h6
  have ht0 : (t : ℝ) ≠ 0 := by
    have : t ≠ 0 := by
      rintro rfl
      exact NeZero.ne n (by simpa using ht)
    exact_mod_cast this
  have hdiv : n / 6 = t := by rw [ht]; exact Nat.mul_div_cancel_left t (by norm_num)
  have h2 : ¬ (2 : ℤ) ∣ ((u : ZMod n).val : ℤ) := not_two_dvd_unit_val ⟨3 * t, by omega⟩ u
  have h3 : ¬ (3 : ℤ) ∣ ((u : ZMod n).val : ℤ) := not_three_dvd_unit_val ⟨2 * t, by omega⟩ u
  rw [twistWeight_natCast, hdiv, ← cos_hexagonal _ h2 h3]
  congr 1
  have hn : (n : ℝ) = 6 * (t : ℝ) := by exact_mod_cast ht
  rw [hn]
  push_cast
  field_simp
  ring

/-- **Theorem 5.5.**  At the hexagonal state the Jacobian is `-(K/(2φ(n)))` times the
Laplacian of `X_n`; hence its spectrum is `-(K/2)(1 - r(M))`, contained in `[-K, -K/4]`
by Theorem 3.2. -/
theorem jac_hex (h6 : 6 ∣ n) (K : ℝ) (f : ZMod n → ℂ) (i : ZMod n) :
    jac n K ((n / 6 : ℕ) : ZMod n) f i
      = -((K / (2 * (Nat.totient n : ℝ)) : ℝ) : ℂ) * lap n f i := by
  unfold jac lap adj
  simp only [twistWeight_hex h6]
  rw [← mul_sum, sum_sub_distrib, sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
  push_cast
  ring

/-- **Theorem 5.5, spectrum.**  `J χ_k = -(K/2)(1 - r(ord k)) χ_k` at the hexagonal state. -/
theorem jac_hex_chi (h6 : 6 ∣ n) (K : ℝ) (k i : ZMod n) :
    jac n K ((n / 6 : ℕ) : ZMod n) (chi n k) i
      = ((-(K / 2) * (1 - r (addOrderOf k)) : ℝ) : ℂ) * chi n k i := by
  have hφ : (Nat.totient n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  rw [jac_hex h6, lap_chi]
  unfold lapEig
  push_cast
  field_simp

/-- **Theorem 5.5, decay rate.**  For `k ≠ 0` the eigenvalue `-(K/2)(1 - r(ord k))` of the
hexagonal Jacobian is at most `-K/4`. -/
theorem jac_hex_eig_le {K : ℝ} (hK : 0 < K) {k : ZMod n} (hk : k ≠ 0) :
    -(K / 2) * (1 - r (addOrderOf k)) ≤ -(K / 4) := by
  have hprimes : ∀ l : ℕ, l.Prime → l ∣ n → l = 2 ∨ 3 ≤ l := by
    intro l hl _
    have := hl.two_le
    omega
  have h := r_le_of_dvd Nat.prime_two Nat.prime_three (by norm_num) hprimes
    (one_lt_addOrderOf hk) (addOrderOf_dvd_self k)
  norm_num at h
  nlinarith

/-! ### Quarter twists (Theorem 5.6 (i)) -/

/-- At a quarter twist `m = n/4` every edge weight is `cos(π u/2) = 0`. -/
theorem twistWeight_quarter (h4 : 4 ∣ n) (u : (ZMod n)ˣ) :
    twistWeight n ((n / 4 : ℕ) : ZMod n) u = 0 := by
  obtain ⟨t, ht⟩ := h4
  have ht0 : (t : ℝ) ≠ 0 := by
    have : t ≠ 0 := by
      rintro rfl
      exact NeZero.ne n (by simpa using ht)
    exact_mod_cast this
  have hdiv : n / 4 = t := by rw [ht]; exact Nat.mul_div_cancel_left t (by norm_num)
  have h2 : ¬ (2 : ℤ) ∣ ((u : ZMod n).val : ℤ) := not_two_dvd_unit_val ⟨2 * t, by omega⟩ u
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ((u : ZMod n).val : ℤ) = 2 * k + 1 := ⟨((u : ZMod n).val : ℤ) / 2, by omega⟩
  rw [twistWeight_natCast, hdiv, ← cos_quarter k]
  congr 1
  have hn : (n : ℝ) = 4 * (t : ℝ) := by exact_mod_cast ht
  have hv : (((u : ZMod n).val : ℕ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by exact_mod_cast hk
  rw [hn]
  push_cast
  push_cast at hv
  rw [hv]
  field_simp
  ring

/-- **Theorem 5.6 (i).**  The Jacobian at a quarter twist vanishes identically. -/
theorem jac_quarter (h4 : 4 ∣ n) (K : ℝ) (f : ZMod n → ℂ) (i : ZMod n) :
    jac n K ((n / 4 : ℕ) : ZMod n) f i = 0 := by
  unfold jac
  simp [twistWeight_quarter h4]

end ArithmeticDynamics

/-! ════════════════════════ Part 8: Classification ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part VIII: completeness of the character spectrum, the natural-step bound
(Proposition 4.7) and the classification theorem for twisted states (Theorem 5.4).
-/

namespace ArithmeticDynamics

open Finset

/-- **Proposition 4.7.**  Every non-trivial eigenvalue `r(M)` of the random-walk matrix
`A/φ(n)` of `X_n` satisfies `|r(M)| ≤ 1/(p-1)`, `p = minFac n`. -/
theorem abs_r_le_of_dvd {n M : ℕ} (hM : 1 < M) (hMn : M ∣ n) :
    |r M| ≤ 1 / ((n.minFac : ℝ) - 1) := by
  have hn1 : n ≠ 1 := by
    rintro rfl
    have := Nat.le_of_dvd Nat.one_pos hMn
    omega
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have hle : n.minFac - 1 ≤ Nat.totient M := minFac_pred_le_totient hM hMn
  have hle' : (n.minFac : ℝ) - 1 ≤ (Nat.totient M : ℝ) := by
    have : ((n.minFac - 1 : ℕ) : ℝ) ≤ (Nat.totient M : ℝ) := by exact_mod_cast hle
    rwa [Nat.cast_sub hp.one_le, Nat.cast_one] at this
  have hpos : (0 : ℝ) < (n.minFac : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
    linarith
  exact (abs_r_le M).trans (one_div_le_one_div_of_le hpos hle')

/-- Elements of additive order `d` in `ℤ/N`, arithmetic form. -/
theorem nat_order_structure {N d v : ℕ} (hN : N ≠ 0) (hv : v < N) (h : N / N.gcd v = d) :
    ∃ c, c < d ∧ Nat.Coprime c d ∧ v = N / d * c := by
  obtain ⟨gg, hgdef⟩ : ∃ gg, N.gcd v = gg := ⟨_, rfl⟩
  rw [hgdef] at h
  have hgN : gg ∣ N := hgdef ▸ Nat.gcd_dvd_left N v
  have hpos : 0 < gg := hgdef ▸ Nat.gcd_pos_of_pos_left v (Nat.pos_of_ne_zero hN)
  have hgg : gg * d = N := by rw [← h]; exact Nat.mul_div_cancel' hgN
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact hN (by simpa using hgg.symm))
  have hdiv : N / d = gg := Nat.div_eq_of_eq_mul_left hd hgg.symm
  obtain ⟨c, hc⟩ : gg ∣ v := hgdef ▸ Nat.gcd_dvd_right N v
  refine ⟨c, ?_, ?_, ?_⟩
  · have h1 : gg * c < gg * d := by rw [← hc, hgg]; exact hv
    exact Nat.lt_of_mul_lt_mul_left h1
  · have e : Nat.gcd (gg * d) (gg * c) = gg := by rw [hgg, ← hc, hgdef]
    rw [Nat.gcd_mul_left] at e
    have e' : gg * Nat.gcd d c = gg * 1 := by rw [e, mul_one]
    have := Nat.eq_of_mul_eq_mul_left hpos e'
    exact Nat.Coprime.symm this
  · rw [hdiv, hc]

variable {n : ℕ} [NeZero n]

theorem exists_coprime_of_addOrderOf {d : ℕ} {m : ZMod n} (h : addOrderOf m = d) :
    ∃ c, c < d ∧ Nat.Coprime c d ∧ m = ((n / d * c : ℕ) : ZMod n) := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have hv : addOrderOf ((m.val : ℕ) : ZMod n) = d := by rw [ZMod.natCast_zmod_val]; exact h
  rw [ZMod.addOrderOf_coe _ hn0] at hv
  obtain ⟨c, hc, hcop, hval⟩ := nat_order_structure hn0 (ZMod.val_lt m) hv
  exact ⟨c, hc, hcop, by rw [← hval, ZMod.natCast_zmod_val]⟩

/-- The elements of order `6` in `ℤ/n` are `±n/6`. -/
theorem eq_of_addOrderOf_eq_six {m : ZMod n} (h : addOrderOf m = 6) :
    m = ((n / 6 : ℕ) : ZMod n) ∨ m = -((n / 6 : ℕ) : ZMod n) := by
  have h6 : 6 ∣ n := h ▸ addOrderOf_dvd_self m
  obtain ⟨c, hc, hcop, hm⟩ := exists_coprime_of_addOrderOf h
  interval_cases c
  · exact absurd hcop (by decide)
  · left; rw [hm, mul_one]
  · exact absurd hcop (by decide)
  · exact absurd hcop (by decide)
  · exact absurd hcop (by decide)
  · right
    rw [hm]
    apply eq_neg_of_add_eq_zero_left
    rw [← Nat.cast_add]
    have e : n / 6 * 5 + n / 6 = n := by
      have := Nat.div_mul_cancel h6
      omega
    rw [e, ZMod.natCast_self]

/-- The elements of order `4` in `ℤ/n` are `±n/4`. -/
theorem eq_of_addOrderOf_eq_four {m : ZMod n} (h : addOrderOf m = 4) :
    m = ((n / 4 : ℕ) : ZMod n) ∨ m = -((n / 4 : ℕ) : ZMod n) := by
  have h4 : 4 ∣ n := h ▸ addOrderOf_dvd_self m
  obtain ⟨c, hc, hcop, hm⟩ := exists_coprime_of_addOrderOf h
  interval_cases c
  · exact absurd hcop (by decide)
  · left; rw [hm, mul_one]
  · exact absurd hcop (by decide)
  · right
    rw [hm]
    apply eq_neg_of_add_eq_zero_left
    rw [← Nat.cast_add]
    have e : n / 4 * 3 + n / 4 = n := by
      have := Nat.div_mul_cancel h4
      omega
    rw [e, ZMod.natCast_self]

/-- The edge weights, and hence the Jacobian, are even in the twist `m`. -/
theorem twistWeight_neg (m : ZMod n) (u : (ZMod n)ˣ) :
    twistWeight n (-m) u = twistWeight n m u := by
  unfold twistWeight
  rw [neg_mul, AddChar.map_neg_eq_conj, Complex.conj_re]

theorem jac_neg (K : ℝ) (m : ZMod n) (f : ZMod n → ℂ) (i : ZMod n) :
    jac n K (-m) f i = jac n K m f i := by
  unfold jac
  simp only [twistWeight_neg]

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
        ∃ ev : ℝ, K / 8 ≤ ev ∧ ∀ i, jac n K m (chi n m) i = (ev : ℂ) * chi n m i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h k hk
    have h6 : 6 ∣ n := h ▸ addOrderOf_dvd_self m
    refine ⟨-(K / 2) * (1 - r (addOrderOf k)), jac_hex_eig_le hK hk, fun i => ?_⟩
    rcases eq_of_addOrderOf_eq_six h with rfl | rfl
    · exact jac_hex_chi h6 K k i
    · rw [jac_neg]
      exact jac_hex_chi h6 K k i
  · intro h f i
    have h4 : 4 ∣ n := h ▸ addOrderOf_dvd_self m
    rcases eq_of_addOrderOf_eq_four h with rfl | rfl
    · exact jac_quarter h4 K f i
    · rw [jac_neg]
      exact jac_quarter h4 K f i
  · intro h4 h6
    exact ⟨K * g (addOrderOf m), (twisted_unstable hK hm h4 h6).1, fun i => jac_chi_self K m i⟩

/-! ### Completeness: the characters carry the whole spectrum of the Laplacian -/

theorem sum_stdAddChar_mul_adj (f : ZMod n → ℂ) (k : ZMod n) :
    ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * adj n f i
      = ramanujan n k * ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * f i := by
  unfold adj ramanujan
  calc ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * ∑ u : (ZMod n)ˣ, f (i + u)
      = ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, ZMod.stdAddChar (-(i * k)) * f (i + u) := by
        simp_rw [mul_sum]
    _ = ∑ u : (ZMod n)ˣ, ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * f (i + u) := sum_comm
    _ = ∑ u : (ZMod n)ˣ, ZMod.stdAddChar (k * (u : ZMod n))
          * ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * f i := by
        refine sum_congr rfl fun u _ => ?_
        rw [← Equiv.sum_comp (Equiv.subRight (u : ZMod n))
          (fun i => ZMod.stdAddChar (-(i * k)) * f (i + (u : ZMod n))), mul_sum]
        refine sum_congr rfl fun j _ => ?_
        have e : -((j - (u : ZMod n)) * k) = k * (u : ZMod n) + -(j * k) := by ring
        simp only [Equiv.subRight_apply, sub_add_cancel]
        rw [e, AddChar.map_add_eq_mul]
        ring
    _ = (∑ u : (ZMod n)ˣ, ZMod.stdAddChar (k * (u : ZMod n)))
          * ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * f i := by
        rw [sum_mul]

/-- **Completeness of the spectrum.**  Every eigenvalue of the Laplacian of `X_n` is one of
the numbers `λ(k) = φ(n)(1 - r(ord k))`; together with `lap_chi` this identifies the
spectrum of `X_n` exactly. -/
theorem lap_eigenvalue (f : ZMod n → ℂ) (c : ℂ) (hf : f ≠ 0)
    (h : ∀ i, lap n f i = c * f i) : ∃ k : ZMod n, c = ((lapEig n k : ℝ) : ℂ) := by
  have hdft : ZMod.dft f ≠ 0 := by
    intro h0
    exact hf ((ZMod.dft (N := n) (E := ℂ)).injective (by rw [h0, map_zero]))
  obtain ⟨k, hk⟩ : ∃ k, ZMod.dft f k ≠ 0 := by
    by_contra hcon
    exact hdft (funext fun k => not_not.mp (not_exists.mp hcon k))
  refine ⟨k, ?_⟩
  have hP : ZMod.dft f k = ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * f i := by
    rw [ZMod.dft_apply]
    simp [smul_eq_mul]
  have h1 : ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * lap n f i = c * ZMod.dft f k := by
    rw [hP, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [h i]
    ring
  have h2 : ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * lap n f i
      = ((lapEig n k : ℝ) : ℂ) * ZMod.dft f k := by
    have : ∀ i : ZMod n, ZMod.stdAddChar (-(i * k)) * lap n f i
        = (Nat.totient n : ℂ) * (ZMod.stdAddChar (-(i * k)) * f i)
          - ZMod.stdAddChar (-(i * k)) * adj n f i := by
      intro i
      unfold lap
      ring
    rw [sum_congr rfl fun i _ => this i, sum_sub_distrib, ← mul_sum, sum_stdAddChar_mul_adj,
      ← hP, ramanujan_eq]
    unfold lapEig
    push_cast
    ring
  exact mul_right_cancel₀ hk (h1.symm.trans h2)

end ArithmeticDynamics

/-! ════════════════════════ Part 9: Rates ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part IX: exact extremal values of r on the divisors of n, the optimal consensus rate and
the universal 3/5 bound (Theorems 3.2 and 4.3, Corollary 4.5 of the paper).
-/

namespace ArithmeticDynamics

open ArithmeticFunction

/-- `p < q` are the two smallest prime divisors of `n`. -/
structure TwoSmallest (n p q : ℕ) : Prop where
  hp : p.Prime
  hq : q.Prime
  hpn : p ∣ n
  hqn : q ∣ n
  hlt : p < q
  least : ∀ l : ℕ, l.Prime → l ∣ n → p ≤ l
  second : ∀ l : ℕ, l.Prime → l ∣ n → l ≠ p → q ≤ l

theorem TwoSmallest.primes {n p q : ℕ} (h : TwoSmallest n p q) :
    ∀ l : ℕ, l.Prime → l ∣ n → l = p ∨ q ≤ l := by
  intro l hl hln
  by_cases hlp : l = p
  · exact Or.inl hlp
  · exact Or.inr (h.second l hl hln hlp)

/-- The values of `r` on the divisors `M > 1` of `n`.  By Hölder's formula these are the
normalised non-trivial adjacency eigenvalues of the unitary Cayley graph `X_n`. -/
def DivSet (n : ℕ) : Set ℝ := {x | ∃ M : ℕ, M ∣ n ∧ 1 < M ∧ r M = x}

/-- **Lemma 3.1(i), sharp form.**  The least value is `-1/(p-1)`, `p = minFac n`. -/
theorem isLeast_divSet {n : ℕ} (hn : 2 ≤ n) :
    IsLeast (DivSet n) (-1 / ((n.minFac : ℝ) - 1)) := by
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  refine ⟨⟨n.minFac, Nat.minFac_dvd n, hp.one_lt, r_prime hp⟩, ?_⟩
  rintro x ⟨M, hMn, hM, rfl⟩
  exact r_ge_of_dvd hM hMn

/-- Every `n ≥ 2` that is not a prime power has two smallest distinct prime divisors. -/
theorem exists_twoSmallest {n : ℕ} (hn : 2 ≤ n) (hpp : ¬ IsPrimePow n) :
    ∃ q : ℕ, TwoSmallest n n.minFac q := by
  have hn0 : n ≠ 0 := by omega
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  set p := n.minFac with hpdef
  have hsplit : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  set c := n / p ^ n.factorization p with hcdef
  have hc1 : c ≠ 1 := by
    intro hc
    apply hpp
    rw [isPrimePow_nat_iff]
    refine ⟨p, n.factorization p, hp, ?_, ?_⟩
    · exact hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
    · rw [hc, mul_one] at hsplit
      exact hsplit
  have hq : c.minFac.Prime := Nat.minFac_prime hc1
  have hcn : c ∣ n := Nat.ordCompl_dvd n p
  have hqn : c.minFac ∣ n := dvd_trans (Nat.minFac_dvd c) hcn
  have hpc : ¬ p ∣ c := Nat.not_dvd_ordCompl hp hn0
  have hne : c.minFac ≠ p := by
    intro h
    exact hpc (h ▸ Nat.minFac_dvd c)
  have hle : p ≤ c.minFac := Nat.minFac_le_of_dvd hq.two_le hqn
  refine ⟨c.minFac, hp, hq, Nat.minFac_dvd n, hqn, lt_of_le_of_ne hle (Ne.symm hne), ?_, ?_⟩
  · intro l hl hln
    exact Nat.minFac_le_of_dvd hl.two_le hln
  · intro l hl hln hlp
    have hcop : Nat.Coprime l (p ^ n.factorization p) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hl hp).mpr hlp)
    have hlc : l ∣ c := by
      rw [← hsplit] at hln
      exact hcop.dvd_of_dvd_mul_left hln
    exact Nat.minFac_le_of_dvd hl.two_le hlc

/-- **Lemma 3.1(ii), sharp form.** -/
theorem isGreatest_divSet_of_twoSmallest {n p q : ℕ} (h : TwoSmallest n p q) :
    IsGreatest (DivSet n) (1 / (((p : ℝ) - 1) * ((q : ℝ) - 1))) := by
  have hne : p ≠ q := by have := h.hlt; omega
  have hcop : Nat.Coprime p q := (Nat.coprime_primes h.hp h.hq).mpr hne
  refine ⟨⟨p * q, hcop.mul_dvd_of_dvd_of_dvd h.hpn h.hqn, ?_, r_mul_primes h.hp h.hq hne⟩, ?_⟩
  · have := h.hp.two_le
    have := h.hq.two_le
    nlinarith
  · rintro x ⟨M, hMn, hM, rfl⟩
    exact r_le_of_dvd h.hp h.hq h.hlt h.primes hM hMn

/-- **Lemma 3.1(iii), sharp form.** -/
theorem isGreatest_divSet_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    IsGreatest (DivSet (p ^ a)) 0 := by
  refine ⟨⟨p ^ 2, pow_dvd_pow p ha, ?_, r_prime_sq hp⟩, ?_⟩
  · have := hp.two_le
    nlinarith
  · rintro x ⟨M, hMn, hM, rfl⟩
    exact r_le_zero_of_dvd_prime_pow hp hM hMn

/-- **Lemma 3.1(iv).** -/
theorem isGreatest_divSet_prime {p : ℕ} (hp : p.Prime) :
    IsGreatest (DivSet p) (-1 / ((p : ℝ) - 1)) := by
  refine ⟨⟨p, dvd_rfl, hp.one_lt, r_prime hp⟩, ?_⟩
  rintro x ⟨M, hMn, hM, rfl⟩
  rcases (Nat.dvd_prime hp).mp hMn with h | h
  · omega
  · rw [h, r_prime hp]

/-! ### The optimal consensus rate -/

/-- `(λ_max - λ₂)/(λ_max + λ₂)` expressed through the extreme values `rmax`, `rmin` of `r`,
using `λ = φ(n) (1 - r)`. -/
noncomputable def rateOf (rmax rmin : ℝ) : ℝ := (rmax - rmin) / (2 - rmax - rmin)

theorem rateOf_eq_laplacian (φ rmax rmin : ℝ) (hφ : φ ≠ 0) :
    (φ * (1 - rmin) - φ * (1 - rmax)) / (φ * (1 - rmin) + φ * (1 - rmax)) = rateOf rmax rmin := by
  unfold rateOf
  have h1 : φ * (1 - rmin) - φ * (1 - rmax) = φ * (rmax - rmin) := by ring
  have h2 : φ * (1 - rmin) + φ * (1 - rmax) = φ * (2 - rmax - rmin) := by ring
  rw [h1, h2, mul_div_mul_left _ _ hφ]

/-- **Theorem 4.3, first case.** -/
theorem rateOf_twoSmallest {p q : ℝ} (hp : 2 ≤ p) (hq : 3 ≤ q) :
    rateOf (1 / ((p - 1) * (q - 1))) (-1 / (p - 1)) = q / (2 * (p - 1) * (q - 1) + q - 2) := by
  unfold rateOf
  have hp' : p - 1 ≠ 0 := by linarith
  have hq' : q - 1 ≠ 0 := by linarith
  have hd : 2 * (p - 1) * (q - 1) + q - 2 ≠ 0 := by nlinarith
  have hd' : 2 - 1 / ((p - 1) * (q - 1)) - -1 / (p - 1) ≠ 0 := by
    have e : 2 - 1 / ((p - 1) * (q - 1)) - -1 / (p - 1)
        = (2 * (p - 1) * (q - 1) + q - 2) / ((p - 1) * (q - 1)) := by
      field_simp
      ring
    rw [e]
    exact div_ne_zero hd (mul_ne_zero hp' hq')
  rw [div_eq_div_iff hd' hd]
  field_simp
  ring

/-- **Theorem 4.3, prime-power case.** -/
theorem rateOf_primePow {p : ℝ} (hp : 2 ≤ p) :
    rateOf 0 (-1 / (p - 1)) = 1 / (2 * p - 1) := by
  unfold rateOf
  have hp' : p - 1 ≠ 0 := by linarith
  have hd : 2 * p - 1 ≠ 0 := by linarith
  have hd' : 2 - 0 - -1 / (p - 1) ≠ 0 := by
    have e : 2 - 0 - -1 / (p - 1) = (2 * p - 1) / (p - 1) := by
      field_simp
      ring
    rw [e]
    exact div_ne_zero hd hp'
  rw [div_eq_div_iff hd' hd]
  field_simp
  ring

/-- **Theorem 4.3, prime case.** -/
theorem rateOf_self (x : ℝ) : rateOf x x = 0 := by simp [rateOf]

/-- `ρ*(X_n)` as a relation: `ρ` is the rate determined by the greatest and least
elements of `DivSet n`. -/
def IsRate (n : ℕ) (ρ : ℝ) : Prop :=
  ∃ rmax rmin : ℝ, IsGreatest (DivSet n) rmax ∧ IsLeast (DivSet n) rmin ∧ ρ = rateOf rmax rmin

theorem IsRate.unique {n : ℕ} {ρ ρ' : ℝ} (h : IsRate n ρ) (h' : IsRate n ρ') : ρ = ρ' := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  obtain ⟨a', b', ha', hb', rfl⟩ := h'
  rw [ha.unique ha', hb.unique hb']

/-- **Theorem 4.3** for `n` with at least two prime divisors. -/
theorem isRate_of_twoSmallest {n p q : ℕ} (hn : 2 ≤ n) (h : TwoSmallest n p q) :
    IsRate n ((q : ℝ) / (2 * ((p : ℝ) - 1) * ((q : ℝ) - 1) + q - 2)) := by
  have hpm : p = n.minFac :=
    le_antisymm (h.least _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n))
      (Nat.minFac_le_of_dvd h.hp.two_le h.hpn)
  refine ⟨_, _, isGreatest_divSet_of_twoSmallest h, isLeast_divSet hn, ?_⟩
  rw [← hpm]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast h.hp.two_le
  have hq3 : (3 : ℝ) ≤ q := by
    have : 3 ≤ q := by have := h.hp.two_le; have := h.hlt; omega
    exact_mod_cast this
  exact (rateOf_twoSmallest hp2 hq3).symm

/-- **Theorem 4.3** for proper prime powers. -/
theorem isRate_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    IsRate (p ^ a) (1 / (2 * (p : ℝ) - 1)) := by
  have h2 : 2 ≤ p ^ a := by
    have := hp.two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right (by omega) (by omega)
  have hmin : (p ^ a).minFac = p := Nat.Prime.pow_minFac hp (by omega)
  refine ⟨_, _, isGreatest_divSet_prime_pow hp ha, isLeast_divSet h2, ?_⟩
  rw [hmin]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact (rateOf_primePow hp2).symm

/-- **Theorem 4.3** for primes. -/
theorem isRate_prime {p : ℕ} (hp : p.Prime) : IsRate p 0 := by
  refine ⟨_, _, isGreatest_divSet_prime hp, isLeast_divSet hp.two_le, ?_⟩
  rw [Nat.Prime.minFac_eq hp, rateOf_self]

/-- **Corollary 4.5.**  For every `n ≥ 2` the optimal rate is at most `3/5`, with equality
if and only if `6 ∣ n`. -/
theorem rate_le_and_eq_iff {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (h : IsRate n ρ) :
    ρ ≤ 3 / 5 ∧ (ρ = 3 / 5 ↔ 6 ∣ n) := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have h6 : ¬ 6 ∣ p ^ k := by
      intro h6
      have h2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by norm_num) h6))).symm
      have h3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h6))).symm
      omega
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      rw [pow_one] at h h6 ⊢
      have := h.unique (isRate_prime hp)
      subst this
      exact ⟨by norm_num, by constructor <;> intro h' <;> [norm_num at h'; exact absurd h' h6]⟩
    · have := h.unique (isRate_prime_pow hp hk2)
      subst this
      have hlt : 1 / (2 * (p : ℝ) - 1) < 3 / 5 := by
        rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
        linarith
      exact ⟨hlt.le, by constructor <;> intro h' <;> [linarith; exact absurd h' h6]⟩
  · obtain ⟨q, hts⟩ := exists_twoSmallest hn hpp
    have := h.unique (isRate_of_twoSmallest hn hts)
    subst this
    set p := n.minFac with hpdef
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hts.hp.two_le
    have hq3n : 3 ≤ q := by have := hts.hp.two_le; have := hts.hlt; omega
    have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq3n
    have hD : (0 : ℝ) < 2 * ((p : ℝ) - 1) * ((q : ℝ) - 1) + q - 2 := by
      have h0 : 0 ≤ ((p : ℝ) - 2) * ((q : ℝ) - 3) := mul_nonneg (by linarith) (by linarith)
      nlinarith [h0]
    have h0 : 0 ≤ ((p : ℝ) - 2) * ((q : ℝ) - 3) := mul_nonneg (by linarith) (by linarith)
    refine ⟨?_, ?_⟩
    · rw [div_le_div_iff₀ hD (by norm_num)]
      nlinarith [h0]
    · constructor
      · intro heq
        rw [div_eq_div_iff hD.ne' (by norm_num)] at heq
        have hp' : (p : ℝ) = 2 := by nlinarith [h0]
        have hq' : (q : ℝ) = 3 := by nlinarith [h0]
        have hpn : p = 2 := by exact_mod_cast hp'
        have hqn : q = 3 := by exact_mod_cast hq'
        have h2 : 2 ∣ n := hpn ▸ hts.hpn
        have h3 : 3 ∣ n := hqn ▸ hts.hqn
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
      · intro h6
        have h2 : 2 ∣ n := dvd_trans (by norm_num) h6
        have h3 : 3 ∣ n := dvd_trans (by norm_num) h6
        have hpn : p = 2 := le_antisymm (hts.least 2 Nat.prime_two h2) hts.hp.two_le
        have hqn : q = 3 :=
          le_antisymm (hts.second 3 Nat.prime_three h3 (by omega)) hq3n
        rw [hpn, hqn]
        norm_num

/-! ### Link with the spectrum of `X_n` -/

/-- `DivSet n` is exactly the set of normalised non-trivial adjacency eigenvalues
`r(ord k)`, `k ≠ 0`, of the unitary Cayley graph `X_n`; equivalently the Laplacian
eigenvalues attached to `k ≠ 0` are the numbers `φ(n)(1 - x)`, `x ∈ DivSet n`. -/
theorem mem_divSet_iff {n : ℕ} [NeZero n] (x : ℝ) :
    x ∈ DivSet n ↔ ∃ k : ZMod n, k ≠ 0 ∧ r (addOrderOf k) = x := by
  constructor
  · rintro ⟨M, hMn, hM, rfl⟩
    exact ⟨((n / M : ℕ) : ZMod n), natCast_div_ne_zero hMn hM, by rw [addOrderOf_natCast_div hMn]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨addOrderOf k, addOrderOf_dvd_self k, one_lt_addOrderOf hk, rfl⟩

end ArithmeticDynamics

/-! ════════════════════════ Part 10: Fourier ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part X: Fourier analysis on `ℤ/n` — orthogonality, Plancherel, and the Laplacian of `X_n`
as a Fourier multiplier; quadratic-form and contraction bounds on sum-zero vectors.
-/

namespace ArithmeticDynamics

open Finset ComplexConjugate

variable {n : ℕ} [NeZero n]

/-- Orthogonality of the characters of `ℤ/n`. -/
theorem sum_stdAddChar_mul (t : ZMod n) :
    ∑ k : ZMod n, (ZMod.stdAddChar (k * t) : ℂ) = if t = 0 then (n : ℂ) else 0 := by
  split_ifs with h
  · subst h
    simp [ZMod.card]
  · have h' : ∑ k : ZMod n, (ZMod.stdAddChar (t * k) : ℂ) = 0 :=
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)
    simpa [mul_comm] using h'

theorem conj_stdAddChar (x : ZMod n) :
    conj (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_conj]

/-- The discrete Fourier coefficient `f̂(k) = ∑_j e(-jk/n) f(j)`. -/
theorem dft_eq (f : ZMod n → ℂ) (k : ZMod n) :
    ZMod.dft f k = ∑ j : ZMod n, ZMod.stdAddChar (-(j * k)) * f j := by
  rw [ZMod.dft_apply]
  simp [smul_eq_mul]

/-- **Plancherel's identity** on `ℤ/n`. -/
theorem plancherel (f g : ZMod n → ℂ) :
    ∑ k : ZMod n, ZMod.dft f k * conj (ZMod.dft g k) = (n : ℂ) * ∑ j : ZMod n, f j * conj (g j) := by
  simp only [dft_eq, map_sum, map_mul, conj_stdAddChar, neg_neg]
  calc ∑ k : ZMod n, (∑ j : ZMod n, ZMod.stdAddChar (-(j * k)) * f j)
          * ∑ l : ZMod n, ZMod.stdAddChar (l * k) * conj (g l)
      = ∑ j : ZMod n, ∑ l : ZMod n, f j * conj (g l)
          * ∑ k : ZMod n, (ZMod.stdAddChar (k * (l - j)) : ℂ) := by
        simp_rw [sum_mul, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun l _ => ?_
        refine sum_congr rfl fun k _ => ?_
        have e : k * (l - j) = -(j * k) + l * k := by ring
        rw [e, AddChar.map_add_eq_mul]
        ring
    _ = ∑ j : ZMod n, f j * conj (g j) * (n : ℂ) := by
        refine sum_congr rfl fun j _ => ?_
        simp_rw [sum_stdAddChar_mul, sub_eq_zero]
        simp [mul_ite, eq_comm]
    _ = (n : ℂ) * ∑ j : ZMod n, f j * conj (g j) := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring

/-- The Laplacian of `X_n` is the Fourier multiplier `λ(k)`. -/
theorem dft_lap (f : ZMod n → ℂ) (k : ZMod n) :
    ZMod.dft (lap n f) k = ((lapEig n k : ℝ) : ℂ) * ZMod.dft f k := by
  rw [dft_eq, dft_eq]
  have : ∀ i : ZMod n, ZMod.stdAddChar (-(i * k)) * lap n f i
      = (Nat.totient n : ℂ) * (ZMod.stdAddChar (-(i * k)) * f i)
        - ZMod.stdAddChar (-(i * k)) * adj n f i := by
    intro i
    unfold lap
    ring
  rw [sum_congr rfl fun i _ => this i, sum_sub_distrib, ← mul_sum, sum_stdAddChar_mul_adj,
    ramanujan_eq]
  unfold lapEig
  push_cast
  ring

/-! ### Real vectors -/

/-- The Laplacian of `X_n` on real vectors. -/
noncomputable def lapR (f : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  (Nat.totient n : ℝ) * f i - ∑ u : (ZMod n)ˣ, f (i + u)

theorem lap_ofReal (f : ZMod n → ℝ) (i : ZMod n) :
    lap n (fun x => (f x : ℂ)) i = ((lapR f i : ℝ) : ℂ) := by
  unfold lap adj lapR
  push_cast
  rfl

/-- The squared Euclidean norm `∑ f_j²`. -/
noncomputable def sqNorm (f : ZMod n → ℝ) : ℝ := ∑ j : ZMod n, f j ^ 2

theorem sqNorm_nonneg (f : ZMod n → ℝ) : 0 ≤ sqNorm f :=
  sum_nonneg fun j _ => sq_nonneg _

theorem sum_normSq_dft (f : ZMod n → ℝ) :
    ∑ k : ZMod n, Complex.normSq (ZMod.dft (fun x => (f x : ℂ)) k) = (n : ℝ) * sqNorm f := by
  have h := plancherel (fun x => (f x : ℂ)) (fun x => (f x : ℂ))
  simp only [Complex.mul_conj, Complex.conj_ofReal] at h
  have h' : ((∑ k : ZMod n, Complex.normSq (ZMod.dft (fun x => (f x : ℂ)) k) : ℝ) : ℂ)
      = (((n : ℝ) * sqNorm f : ℝ) : ℂ) := by
    push_cast
    rw [h]
    unfold sqNorm
    push_cast
    congr 1
    refine sum_congr rfl fun j _ => ?_
    ring
  exact_mod_cast h'

theorem dft_zero_of_sum_zero (f : ZMod n → ℝ) (hf : ∑ j, f j = 0) :
    ZMod.dft (fun x => (f x : ℂ)) 0 = 0 := by
  rw [ZMod.dft_apply_zero]
  exact_mod_cast hf

theorem sum_lapR (f : ZMod n → ℝ) : ∑ j : ZMod n, lapR f j = 0 := by
  unfold lapR
  rw [sum_sub_distrib, ← mul_sum, sum_comm]
  have : ∀ u : (ZMod n)ˣ, ∑ j : ZMod n, f (j + u) = ∑ j : ZMod n, f j := fun u =>
    Equiv.sum_comp (Equiv.addRight (u : ZMod n)) f
  rw [sum_congr rfl fun u _ => this u, sum_const, card_univ, ZMod.card_units_eq_totient,
    nsmul_eq_mul]
  ring

/-- **Spectral contraction.**  If `|1 - ε λ(k)| ≤ ρ` for every `k ≠ 0`, then on sum-zero vectors
the map `f ↦ f - ε L f` contracts the squared norm by `ρ²`. -/
theorem sqNorm_step_le (f : ZMod n → ℝ) (hf : ∑ j, f j = 0) {ε ρ : ℝ}
    (hρ : ∀ k : ZMod n, k ≠ 0 → |1 - ε * lapEig n k| ≤ ρ) :
    sqNorm (fun j => f j - ε * lapR f j) ≤ ρ ^ 2 * sqNorm f := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set g : ZMod n → ℝ := fun j => f j - ε * lapR f j with hg
  have hdft : ∀ k, ZMod.dft (fun x => (g x : ℂ)) k
      = ((1 - ε * lapEig n k : ℝ) : ℂ) * ZMod.dft (fun x => (f x : ℂ)) k := by
    intro k
    have e : (fun x => (g x : ℂ)) = (fun x => (f x : ℂ)) - (ε : ℂ) • lap n (fun x => (f x : ℂ)) := by
      funext x
      simp only [hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lap_ofReal]
      push_cast
      ring
    rw [e, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, dft_lap, smul_eq_mul]
    push_cast
    ring
  have key : ∀ k : ZMod n, Complex.normSq (ZMod.dft (fun x => (g x : ℂ)) k)
      ≤ ρ ^ 2 * Complex.normSq (ZMod.dft (fun x => (f x : ℂ)) k) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [hdft, dft_zero_of_sum_zero f hf]
      simp
    · rw [hdft, Complex.normSq_mul, Complex.normSq_ofReal]
      have h1 := hρ k hk
      have h2 : (1 - ε * lapEig n k) * (1 - ε * lapEig n k) ≤ ρ ^ 2 := by
        rw [← sq, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      exact mul_le_mul_of_nonneg_right h2 (Complex.normSq_nonneg _)
  have hsum := sum_le_sum fun k (_ : k ∈ (univ : Finset (ZMod n))) => key k
  rw [← mul_sum, sum_normSq_dft, sum_normSq_dft] at hsum
  have : (n : ℝ) * sqNorm g ≤ (n : ℝ) * (ρ ^ 2 * sqNorm f) := by linarith
  exact le_of_mul_le_mul_left this hn

/-- **Quadratic-form bounds.**  If `c ≤ λ(k) ≤ C` for every `k ≠ 0`, then for sum-zero `f`,
`c ∑ f² ≤ ∑ (Lf) f ≤ C ∑ f²`. -/
theorem quadForm_bounds (f : ZMod n → ℝ) (hf : ∑ j, f j = 0) {c C : ℝ}
    (hc : ∀ k : ZMod n, k ≠ 0 → c ≤ lapEig n k) (hC : ∀ k : ZMod n, k ≠ 0 → lapEig n k ≤ C) :
    c * sqNorm f ≤ ∑ j, lapR f j * f j ∧ ∑ j, lapR f j * f j ≤ C * sqNorm f := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set F : ZMod n → ℂ := ZMod.dft (fun x => (f x : ℂ)) with hF
  have hP := plancherel (lap n (fun x => (f x : ℂ))) (fun x => (f x : ℂ))
  simp only [dft_lap, lap_ofReal, Complex.conj_ofReal] at hP
  have hQ : (n : ℝ) * ∑ j, lapR f j * f j = ∑ k, lapEig n k * Complex.normSq (F k) := by
    have : ∀ k, ((lapEig n k : ℝ) : ℂ) * F k * conj (F k)
        = ((lapEig n k * Complex.normSq (F k) : ℝ) : ℂ) := by
      intro k
      rw [mul_assoc, Complex.mul_conj]
      push_cast
      ring
    simp only [← hF, this] at hP
    have h' : ((∑ k, lapEig n k * Complex.normSq (F k) : ℝ) : ℂ)
        = (((n : ℝ) * ∑ j, lapR f j * f j : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, hP]
      push_cast
      rfl
    exact_mod_cast h'.symm
  have hF0 : F 0 = 0 := dft_zero_of_sum_zero f hf
  have hN := sum_normSq_dft f
  rw [← hF] at hN
  have lo : ∀ k, c * Complex.normSq (F k) ≤ lapEig n k * Complex.normSq (F k) := by
    intro k
    by_cases hk : k = 0
    · simp [hk, hF0]
    · exact mul_le_mul_of_nonneg_right (hc k hk) (Complex.normSq_nonneg _)
  have up : ∀ k, lapEig n k * Complex.normSq (F k) ≤ C * Complex.normSq (F k) := by
    intro k
    by_cases hk : k = 0
    · simp [hk, hF0]
    · exact mul_le_mul_of_nonneg_right (hC k hk) (Complex.normSq_nonneg _)
  have s1 := sum_le_sum fun k (_ : k ∈ (univ : Finset (ZMod n))) => lo k
  have s2 := sum_le_sum fun k (_ : k ∈ (univ : Finset (ZMod n))) => up k
  rw [← mul_sum, hN, ← hQ] at s1
  rw [← mul_sum, hN, ← hQ] at s2
  constructor
  · nlinarith
  · nlinarith

end ArithmeticDynamics

/-! ════════════════════════ Part 11: Multiplicity ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XI: equality cases of Lemma 3.1, exact multiplicities in Theorem 3.2, and the
spectral ratio of Corollary 3.3.
-/

namespace ArithmeticDynamics

open ArithmeticFunction Finset

/-- A squarefree non-prime `M > 1` is divisible by two distinct primes. -/
theorem two_primes_of_not_prime {M : ℕ} (hM : 1 < M) (hsq : Squarefree M) (hnp : ¬ M.Prime) :
    ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a ≠ b ∧ a * b ∣ M := by
  have ha : M.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨m, hm⟩ := Nat.minFac_dvd M
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hnp (hm ▸ ha)
  have hb : m.minFac.Prime := Nat.minFac_prime hm1
  refine ⟨M.minFac, m.minFac, ha, hb, ?_, ?_⟩
  · intro heq
    have hdvd : M.minFac * M.minFac ∣ M := by
      conv_rhs => rw [hm]
      exact Nat.mul_dvd_mul_left _ (heq ▸ Nat.minFac_dvd m)
    exact ha.one_lt.ne' (Nat.isUnit_iff.mp (hsq _ hdvd))
  · conv_rhs => rw [hm]
    exact Nat.mul_dvd_mul_left _ (Nat.minFac_dvd m)

theorem totient_ge_of_two_primes {M a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (hdvd : a * b ∣ M) (hM : 0 < M) : (a - 1) * (b - 1) ≤ Nat.totient M := by
  have hcop : Nat.Coprime a b := (Nat.coprime_primes ha hb).mpr hab
  have hd := Nat.totient_dvd_of_dvd hdvd
  rw [Nat.totient_mul hcop, Nat.totient_prime ha, Nat.totient_prime hb] at hd
  exact Nat.le_of_dvd (Nat.totient_pos.mpr hM) hd

/-- **Lemma 3.1 (i), equality case.**  `r M = -1/(p-1)` for a divisor `M > 1` of `n` iff `M = p`. -/
theorem r_eq_min_iff {n M : ℕ} (hM : 1 < M) (hMn : M ∣ n) :
    r M = -1 / ((n.minFac : ℝ) - 1) ↔ M = n.minFac := by
  have hn1 : n ≠ 1 := by
    rintro rfl
    have := Nat.le_of_dvd Nat.one_pos hMn
    omega
  have hp := Nat.minFac_prime hn1
  constructor
  · intro h
    set p := n.minFac with hpdef
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      linarith
    have hneg : r M < 0 := by
      rw [h, neg_div]
      exact neg_neg_of_pos (by positivity)
    have hμ : moebius M = -1 := by
      rcases moebius_eq_or M with h0 | h0 | h0
      · simp [r, h0] at hneg
      · have : 0 ≤ r M := by simp [r, h0]
        linarith
      · exact h0
    have hφ : Nat.totient M = p - 1 := by
      rw [r, hμ] at h
      have hφpos : (0 : ℝ) < (Nat.totient M : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      have e : (Nat.totient M : ℝ) = (p : ℝ) - 1 := by
        field_simp at h
        push_cast at h
        linarith
      have : ((Nat.totient M : ℕ) : ℝ) = ((p - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hp.one_le, Nat.cast_one]
        exact e
      exact_mod_cast this
    have hsq : Squarefree M := moebius_ne_zero_iff_squarefree.mp (by rw [hμ]; norm_num)
    by_cases hpr : M.Prime
    · have : M - 1 = p - 1 := by rw [← Nat.totient_prime hpr, hφ]
      have := hpr.two_le
      have := hp.two_le
      omega
    · exfalso
      obtain ⟨a, b, ha, hb, hab, hdvd⟩ := two_primes_of_not_prime hM hsq hpr
      have hle := totient_ge_of_two_primes ha hb hab hdvd (by omega)
      have han : a ∣ n := dvd_trans (dvd_trans (Dvd.intro _ rfl) hdvd) hMn
      have hbn : b ∣ n := dvd_trans (dvd_trans (Dvd.intro_left _ rfl) hdvd) hMn
      have hpa : p ≤ a := Nat.minFac_le_of_dvd ha.two_le han
      have hpb : p ≤ b := Nat.minFac_le_of_dvd hb.two_le hbn
      have hp2 := hp.two_le
      rw [hφ] at hle
      rcases Nat.lt_or_gt_of_ne hab with h' | h'
      · have h1 : (p - 1) * 2 ≤ (a - 1) * (b - 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      · have h1 : 2 * (p - 1) ≤ (a - 1) * (b - 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
  · rintro rfl
    exact r_minFac hn1

/-- **Lemma 3.1 (ii), equality case.**  If `p < q` are the two smallest prime divisors of `n`,
then `r M = 1/((p-1)(q-1))` for a divisor `M > 1` of `n` iff `M = p q`. -/
theorem r_eq_max_iff {n p q M : ℕ} (h : TwoSmallest n p q) (hM : 1 < M) (hMn : M ∣ n) :
    r M = 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)) ↔ M = p * q := by
  have hne : p ≠ q := by have := h.hlt; omega
  constructor
  · intro hr
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.hp.two_le
      linarith
    have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h.hq.two_le
      linarith
    have hpos : 0 < r M := by rw [hr]; positivity
    have hμ : moebius M = 1 := by
      rcases moebius_eq_or M with h0 | h0 | h0
      · simp [r, h0] at hpos
      · exact h0
      · have : r M ≤ 0 := by
          simp only [r, h0]
          push_cast
          rw [neg_div]
          exact neg_nonpos.mpr (by positivity)
        linarith
    have hφ : Nat.totient M = (p - 1) * (q - 1) := by
      rw [r, hμ] at hr
      have hφpos : (0 : ℝ) < (Nat.totient M : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      have e : (Nat.totient M : ℝ) = ((p : ℝ) - 1) * ((q : ℝ) - 1) := by
        field_simp at hr
        push_cast at hr
        linarith
      have : ((Nat.totient M : ℕ) : ℝ) = (((p - 1) * (q - 1) : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub h.hp.one_le, Nat.cast_sub h.hq.one_le, Nat.cast_one]
        exact e
      exact_mod_cast this
    have hsq : Squarefree M := moebius_ne_zero_iff_squarefree.mp (by rw [hμ]; norm_num)
    obtain ⟨a, b, ha, hb, hab, hdvd⟩ := exists_two_primes_of_moebius_eq_one hM hμ
    have hle := totient_ge_of_two_primes ha hb hab hdvd (by omega)
    rw [hφ] at hle
    have han : a ∣ n := dvd_trans (dvd_trans (Dvd.intro _ rfl) hdvd) hMn
    have hbn : b ∣ n := dvd_trans (dvd_trans (Dvd.intro_left _ rfl) hdvd) hMn
    have hp2 := h.hp.two_le
    have hlt := h.hlt
    -- the pair `{a, b}` must be `{p, q}`
    have hpq : a * b = p * q := by
      rcases h.primes a ha han with ha' | ha' <;> rcases h.primes b hb hbn with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · subst ha'
        have : (a - 1) * (b - 1) ≤ (a - 1) * (q - 1) := hle
        have h3 : b - 1 ≤ q - 1 := Nat.le_of_mul_le_mul_left this (by omega)
        have : b = q := by omega
        rw [this]
      · subst hb'
        have : (b - 1) * (a - 1) ≤ (b - 1) * (q - 1) := by rw [Nat.mul_comm]; exact hle
        have h3 : a - 1 ≤ q - 1 := Nat.le_of_mul_le_mul_left this (by omega)
        have : a = q := by omega
        rw [this, Nat.mul_comm]
      · exfalso
        rcases Nat.lt_or_gt_of_ne hab with h' | h'
        · have h1 : (q - 1) * q ≤ (a - 1) * (b - 1) := Nat.mul_le_mul (by omega) (by omega)
          have h2 : (p - 1) * (q - 1) < (q - 1) * q := by
            rw [Nat.mul_comm]
            exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
          omega
        · have h1 : q * (q - 1) ≤ (a - 1) * (b - 1) := Nat.mul_le_mul (by omega) (by omega)
          have h2 : (p - 1) * (q - 1) < q * (q - 1) :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
          omega
    rw [hpq] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hcop : Nat.Coprime (p * q) c := by
      rw [hc] at hsq
      exact Nat.coprime_of_squarefree_mul hsq
    have hcop2 : Nat.Coprime p q := (Nat.coprime_primes h.hp h.hq).mpr hne
    have hφc : Nat.totient c = 1 := by
      have e := hφ
      rw [hc, Nat.totient_mul hcop, Nat.totient_mul hcop2, Nat.totient_prime h.hp,
        Nat.totient_prime h.hq] at e
      have hpos : 0 < (p - 1) * (q - 1) := Nat.mul_pos (by omega) (by omega)
      have : (p - 1) * (q - 1) * Nat.totient c = (p - 1) * (q - 1) * 1 := by rw [e, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hpos this
    rcases Nat.totient_eq_one_iff.mp hφc with hc1 | hc2
    · rw [hc, hc1, mul_one]
    · exfalso
      have e := hμ
      rw [hc, hc2, isMultiplicative_moebius.map_mul_of_coprime (hc2 ▸ hcop),
        isMultiplicative_moebius.map_mul_of_coprime hcop2, moebius_apply_prime h.hp,
        moebius_apply_prime h.hq, moebius_apply_prime Nat.prime_two] at e
      norm_num at e
  · rintro rfl
    exact r_mul_primes h.hp h.hq hne

/-- **Lemma 3.1 (iii), equality case.**  For `n = p^a` and a divisor `M > 1` of `n`,
`r M = 0` iff `M ≠ p`. -/
theorem r_eq_zero_iff_prime_pow {p a M : ℕ} (hp : p.Prime) (hM : 1 < M) (hMn : M ∣ p ^ a) :
    r M = 0 ↔ M ≠ p := by
  obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hMn
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hM
  constructor
  · intro h0 heq
    rw [heq, r_prime hp] at h0
    have : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      linarith
    rw [neg_div] at h0
    have : (1 : ℝ) / ((p : ℝ) - 1) > 0 := by positivity
    linarith
  · intro hne
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hne (pow_one p)
    rw [r, moebius_apply_prime_pow hp hk]
    simp [hk1]

/-! ### Counting residues of a given additive order -/

theorem card_addOrderOf_eq {n d : ℕ} [NeZero n] (hd : d ∣ n) :
    #(univ.filter (fun k : ZMod n => addOrderOf k = d)) = Nat.totient d := by
  classical
  have := IsAddCyclic.card_addOrderOf_eq_totient (α := ZMod n) (d := d) (by simpa [ZMod.card] using hd)
  simpa using this

variable {n : ℕ} [NeZero n]

theorem lapEig_eq_iff (k : ZMod n) (x : ℝ) :
    lapEig n k = (Nat.totient n : ℝ) * (1 - x) ↔ r (addOrderOf k) = x := by
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  unfold lapEig
  constructor
  · intro h
    have := mul_left_cancel₀ hφ.ne' h
    linarith
  · intro h
    rw [h]

omit [NeZero n] in
theorem lapEig_zero : lapEig n 0 = 0 := by
  unfold lapEig
  rw [addOrderOf_zero, r_one]
  ring

/-- **Theorem 3.2, multiplicity of `λ_max`.**  Exactly `p - 1` residues carry `λ_max`. -/
theorem card_lapEig_max (hn : 1 < n) :
    #(univ.filter (fun k : ZMod n =>
        lapEig n k = (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1))))
      = n.minFac - 1 := by
  classical
  have hn1 : n ≠ 1 := by omega
  have hp := Nat.minFac_prime hn1
  have hp1 : (n.minFac : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have e : (n.minFac : ℝ) / ((n.minFac : ℝ) - 1) = 1 - (-1 / ((n.minFac : ℝ) - 1)) := by
    field_simp
    ring
  have hset : univ.filter (fun k : ZMod n =>
        lapEig n k = (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1)))
      = univ.filter (fun k : ZMod n => addOrderOf k = n.minFac) := by
    ext k
    simp only [mem_filter, mem_univ, true_and]
    rw [e, lapEig_eq_iff]
    by_cases hk : k = 0
    · subst hk
      rw [addOrderOf_zero, r_one]
      constructor
      · intro h
        have : (0 : ℝ) < 1 / ((n.minFac : ℝ) - 1) := by
          have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
          have : (0 : ℝ) < (n.minFac : ℝ) - 1 := by linarith
          positivity
        rw [neg_div] at h
        linarith
      · intro h
        exact absurd h.symm hp.one_lt.ne'
    · exact r_eq_min_iff (one_lt_addOrderOf hk) (addOrderOf_dvd_self k)
  rw [hset, card_addOrderOf_eq (Nat.minFac_dvd n), Nat.totient_prime hp]

/-- **Theorem 3.2, multiplicity of `λ₂` when `ω(n) ≥ 2`.**  Exactly `(p-1)(q-1)` residues. -/
theorem card_lapEig_two_primes {p q : ℕ} (h : TwoSmallest n p q) :
    #(univ.filter (fun k : ZMod n =>
        k ≠ 0 ∧ lapEig n k = (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)))))
      = (p - 1) * (q - 1) := by
  classical
  have hne : p ≠ q := by have := h.hlt; omega
  have hcop : Nat.Coprime p q := (Nat.coprime_primes h.hp h.hq).mpr hne
  have hpq : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd h.hpn h.hqn
  have hset : univ.filter (fun k : ZMod n =>
        k ≠ 0 ∧ lapEig n k = (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1))))
      = univ.filter (fun k : ZMod n => addOrderOf k = p * q) := by
    ext k
    simp only [mem_filter, mem_univ, true_and]
    rw [lapEig_eq_iff]
    constructor
    · rintro ⟨hk, hr⟩
      exact (r_eq_max_iff h (one_lt_addOrderOf hk) (addOrderOf_dvd_self k)).mp hr
    · intro hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [addOrderOf_zero] at hk
        have := Nat.mul_le_mul h.hp.two_le h.hq.two_le
        omega
      exact ⟨hk0, (r_eq_max_iff h (one_lt_addOrderOf hk0) (addOrderOf_dvd_self k)).mpr hk⟩
  rw [hset, card_addOrderOf_eq hpq, Nat.totient_mul hcop, Nat.totient_prime h.hp,
    Nat.totient_prime h.hq]

/-- **Theorem 3.2, multiplicity of `λ₂` for `n = p^a`, `a ≥ 2`.**  Exactly `p^a - p` residues. -/
theorem card_lapEig_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (hn : n = p ^ a) :
    #(univ.filter (fun k : ZMod n => k ≠ 0 ∧ lapEig n k = (Nat.totient n : ℝ)))
      = p ^ a - p := by
  classical
  have hpn : p ∣ n := by
    rw [hn]
    exact dvd_pow_self p (by omega)
  have hdvd : ∀ k : ZMod n, addOrderOf k ∣ p ^ a := fun k => by
    rw [← hn]
    exact addOrderOf_dvd_self k
  have hset : univ.filter (fun k : ZMod n => k ≠ 0 ∧ lapEig n k = (Nat.totient n : ℝ))
      = (univ.filter (fun k : ZMod n => addOrderOf k ≠ 1)) \
          univ.filter (fun k : ZMod n => addOrderOf k = p) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    have e : (Nat.totient n : ℝ) = (Nat.totient n : ℝ) * (1 - 0) := by ring
    rw [e, lapEig_eq_iff]
    rw [ne_eq, ← AddMonoid.addOrderOf_eq_one_iff.not]
    constructor
    · rintro ⟨hk, hr⟩
      have hk' : k ≠ 0 := fun h0 => hk (by rw [h0, addOrderOf_zero])
      exact ⟨hk, (r_eq_zero_iff_prime_pow hp (one_lt_addOrderOf hk') (hdvd k)).mp hr⟩
    · rintro ⟨hk, hkp⟩
      have hk' : k ≠ 0 := fun h0 => hk (by rw [h0, addOrderOf_zero])
      exact ⟨hk, (r_eq_zero_iff_prime_pow hp (one_lt_addOrderOf hk') (hdvd k)).mpr hkp⟩
  have hsub : univ.filter (fun k : ZMod n => addOrderOf k = p)
      ⊆ univ.filter (fun k : ZMod n => addOrderOf k ≠ 1) := by
    intro k
    simp only [mem_filter, mem_univ, true_and]
    intro hk
    rw [hk]
    exact hp.one_lt.ne'
  have hcompl : univ.filter (fun k : ZMod n => addOrderOf k ≠ 1)
      = univ \ univ.filter (fun k : ZMod n => addOrderOf k = 1) := by
    ext k
    simp
  rw [hset, card_sdiff_of_subset hsub, hcompl, card_sdiff_of_subset (subset_univ _),
    card_addOrderOf_eq (one_dvd n), card_addOrderOf_eq hpn, card_univ, ZMod.card,
    Nat.totient_one, Nat.totient_prime hp, hn]
  have : p ≤ p ^ a := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos (by omega)
  have := hp.two_le
  omega

/-- **Theorem 3.2, prime case.**  For `n = p` prime every `k ≠ 0` has eigenvalue `n`. -/
theorem lapEig_prime (hp : n.Prime) (k : ZMod n) (hk : k ≠ 0) : lapEig n k = n := by
  have hord : addOrderOf k = n := by
    rcases (Nat.dvd_prime hp).mp (addOrderOf_dvd_self k) with h1 | h1
    · exact absurd h1 (one_lt_addOrderOf hk).ne'
    · exact h1
  unfold lapEig
  rw [hord, r_prime hp, Nat.totient_prime hp]
  have : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    linarith
  rw [Nat.cast_sub hp.one_le]
  push_cast
  field_simp
  ring

/-! ### Corollary 3.3: the spectral ratio -/

/-- **Corollary 3.3, formula.**  `λ₂/λ_max = ((p-1)(q-1) - 1)/(p(q-1))` when `ω(n) ≥ 2`. -/
theorem spectral_ratio_formula {p q : ℝ} (hp : 2 ≤ p) (hq : 3 ≤ q) :
    (1 - 1 / ((p - 1) * (q - 1))) / (1 - (-1 / (p - 1)))
      = ((p - 1) * (q - 1) - 1) / (p * (q - 1)) := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : q - 1 ≠ 0 := by linarith
  have h3 : p ≠ 0 := by linarith
  have hA : 1 - (-1 / (p - 1)) ≠ 0 := by
    have : 1 - (-1 / (p - 1)) = p / (p - 1) := by field_simp; ring
    rw [this]
    exact div_ne_zero h3 h1
  have hB : p * (q - 1) ≠ 0 := mul_ne_zero h3 h2
  rw [div_eq_div_iff hA hB]
  field_simp
  ring

/-- **Corollary 3.3.**  For every `n ≥ 2`, `λ₂/λ_max = (1 - r_max)/(1 - r_min) ≥ 1/4`,
with equality iff `6 ∣ n`. -/
theorem spectral_ratio {m : ℕ} (hm : 2 ≤ m) {rmax rmin : ℝ} (hmax : IsGreatest (DivSet m) rmax)
    (hmin : IsLeast (DivSet m) rmin) :
    1 / 4 ≤ (1 - rmax) / (1 - rmin) ∧ ((1 - rmax) / (1 - rmin) = 1 / 4 ↔ 6 ∣ m) := by
  have hrmin := hmin.unique (isLeast_divSet hm)
  subst hrmin
  set p := m.minFac with hpdef
  have hp := Nat.minFac_prime (show m ≠ 1 by omega)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : (1 : ℝ) - (-1 / ((p : ℝ) - 1)) = p / ((p : ℝ) - 1) := by
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  by_cases hpp : IsPrimePow m
  · obtain ⟨p', k, hp', hk, hpk⟩ := (isPrimePow_nat_iff m).mp hpp
    have hmin' : m.minFac = p' := by rw [← hpk]; exact Nat.Prime.pow_minFac hp' (by omega)
    have h6 : ¬ 6 ∣ m := by
      intro h6
      rw [← hpk] at h6
      have h2 : p' = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp').mp
        (Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by norm_num) h6))).symm
      have h3 : p' = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp').mp
        (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h6))).symm
      omega
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      rw [pow_one] at hpk
      subst hpk
      have hrmax := hmax.unique (isGreatest_divSet_prime hp')
      subst hrmax
      have : (1 - (-1 / ((p : ℝ) - 1))) / (1 - (-1 / ((p : ℝ) - 1))) = 1 := by
        rw [div_self]
        rw [hden]
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        positivity
      have hpeq : p = p' := hpdef.trans hmin'
      rw [hpeq] at this
      rw [hpeq, this]
      exact ⟨by norm_num, by constructor <;> intro h' <;> [norm_num at h'; exact absurd h' h6]⟩
    · rw [← hpk] at hmax
      have hrmax := hmax.unique (isGreatest_divSet_prime_pow hp' hk2)
      subst hrmax
      rw [hden, hpdef, hmin']
      have hp'2 : (2 : ℝ) ≤ p' := by exact_mod_cast hp'.two_le
      have hval : (1 - 0) / ((p' : ℝ) / ((p' : ℝ) - 1)) = ((p' : ℝ) - 1) / p' := by
        have : (p' : ℝ) - 1 ≠ 0 := by linarith
        have : (p' : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      rw [hval]
      have hgt : (1 : ℝ) / 4 < ((p' : ℝ) - 1) / p' := by
        rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
        linarith
      exact ⟨hgt.le, by constructor <;> intro h' <;> [linarith; exact absurd h' h6]⟩
  · obtain ⟨q, hts⟩ := exists_twoSmallest hm hpp
    have hrmax := hmax.unique (isGreatest_divSet_of_twoSmallest hts)
    subst hrmax
    have hq3n : 3 ≤ q := by have := hts.hp.two_le; have := hts.hlt; omega
    have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq3n
    rw [← hpdef, spectral_ratio_formula hp2 hq3]
    have hD : (0 : ℝ) < p * ((q : ℝ) - 1) := by nlinarith
    have h0 : 0 ≤ ((p : ℝ) - 2) * ((q : ℝ) - 3) := mul_nonneg (by linarith) (by linarith)
    refine ⟨?_, ?_⟩
    · rw [div_le_div_iff₀ (by norm_num) hD]
      nlinarith
    · constructor
      · intro heq
        rw [div_eq_div_iff hD.ne' (by norm_num)] at heq
        have hp' : (p : ℝ) = 2 := by nlinarith
        have hq' : (q : ℝ) = 3 := by nlinarith
        have hpn : p = 2 := by exact_mod_cast hp'
        have hqn : q = 3 := by exact_mod_cast hq'
        have h2 : 2 ∣ m := by
          have e : m.minFac = 2 := hpn
          rw [← e]
          exact Nat.minFac_dvd m
        have h3 : 3 ∣ m := by have := hts.hqn; rwa [hqn] at this
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
      · intro h6
        have h2 : 2 ∣ m := dvd_trans (by norm_num) h6
        have h3 : 3 ∣ m := dvd_trans (by norm_num) h6
        have hpn : p = 2 := le_antisymm (hts.least 2 Nat.prime_two h2) hts.hp.two_le
        have hqn : q = 3 := le_antisymm (hts.second 3 Nat.prime_three h3 (by omega)) hq3n
        rw [hpn, hqn]
        norm_num

end ArithmeticDynamics

/-! ════════════════════════ Part 12: ConsensusDynamics ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XII: consensus dynamics on `X_n` — the discrete iteration with its exact contraction
(Lemma 4.1, Theorem 4.3), the optimal step (4.6), the universal bound and iteration count
(Corollary 4.5), the natural step (Proposition 4.7), and the continuous-time flow (Remark 4.8).
-/

namespace ArithmeticDynamics

open Finset ArithmeticFunction

variable {n : ℕ} [NeZero n]

/-- The average `x̄ = (1/n) ∑ x_j`. -/
noncomputable def avg (x : ZMod n → ℝ) : ℝ := (∑ j, x j) / n

/-- The consensus error `x - x̄ 1`. -/
noncomputable def err (x : ZMod n → ℝ) : ZMod n → ℝ := fun j => x j - avg x

/-- One step of the consensus iteration `x ↦ (I - ε L) x` on `X_n`. -/
noncomputable def step (ε : ℝ) (x : ZMod n → ℝ) : ZMod n → ℝ := fun j => x j - ε * lapR x j

theorem sum_err (x : ZMod n → ℝ) : ∑ j, err x j = 0 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  unfold err avg
  rw [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  field_simp
  ring

theorem lapR_sub_const (x : ZMod n → ℝ) (c : ℝ) : lapR (fun j => x j - c) = lapR x := by
  funext i
  unfold lapR
  rw [sum_sub_distrib, sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
  ring

theorem sum_step (ε : ℝ) (x : ZMod n → ℝ) : ∑ j, step ε x j = ∑ j, x j := by
  unfold step
  rw [sum_sub_distrib, ← mul_sum, sum_lapR, mul_zero, sub_zero]

theorem avg_step (ε : ℝ) (x : ZMod n → ℝ) : avg (step ε x) = avg x := by
  unfold avg
  rw [sum_step]

theorem err_step (ε : ℝ) (x : ZMod n → ℝ) : err (step ε x) = step ε (err x) := by
  funext j
  unfold err
  rw [avg_step]
  change step ε x j - avg x = step ε (fun j => x j - avg x) j
  unfold step
  rw [lapR_sub_const]
  ring

/-- **Lemma 4.1 / Theorem 4.3, the norm estimate.**  If `|1 - ε λ(k)| ≤ ρ` for all `k ≠ 0`, then
`‖x(t) - x̄ 1‖² ≤ ρ^{2t} ‖x(0) - x̄ 1‖²` for the iteration `x(t+1) = (I - εL) x(t)`. -/
theorem sqNorm_err_iterate {ε ρ : ℝ} (hρ : ∀ k : ZMod n, k ≠ 0 → |1 - ε * lapEig n k| ≤ ρ)
    (x : ZMod n → ℝ) (t : ℕ) :
    sqNorm (err ((step ε)^[t] x)) ≤ (ρ ^ 2) ^ t * sqNorm (err x) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', err_step, pow_succ]
    calc sqNorm (step ε (err ((step ε)^[t] x)))
        ≤ ρ ^ 2 * sqNorm (err ((step ε)^[t] x)) := sqNorm_step_le _ (sum_err _) hρ
      _ ≤ ρ ^ 2 * ((ρ ^ 2) ^ t * sqNorm (err x)) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = (ρ ^ 2) ^ t * ρ ^ 2 * sqNorm (err x) := by ring

theorem r_le_half_of_one_lt {M : ℕ} (hM : 1 < M) : r M ≤ 1 / 2 := by
  by_cases h2 : M = 2
  · subst h2
    rw [r_two]
    norm_num
  · exact (abs_le.mp (abs_r_le_half (by omega))).2

/-- **Theorem 4.3, dynamical form.**  If `ρ` is the optimal rate of `X_n` (`IsRate n ρ`), then the
iteration with the optimal step `ε* = 2/(λ₂ + λ_max)` satisfies
`‖x(t) - x̄ 1‖² ≤ ρ^{2t} ‖x(0) - x̄ 1‖²` for every initial vector. -/
theorem consensus_of_isRate {ρ : ℝ} (h : IsRate n ρ) :
    ∃ ε > 0, ∀ (x : ZMod n → ℝ) (t : ℕ),
      sqNorm (err ((step ε)^[t] x)) ≤ (ρ ^ 2) ^ t * sqNorm (err x) := by
  obtain ⟨rmax, rmin, hmax, hmin, rfl⟩ := h
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨M, hMn, hM, hrM⟩ := hmax.1
  have hrmax : rmax ≤ 1 / 2 := hrM ▸ r_le_half_of_one_lt hM
  have hle : rmin ≤ rmax := hmin.2 hmax.1
  set a := (Nat.totient n : ℝ) * (1 - rmax) with ha
  set b := (Nat.totient n : ℝ) * (1 - rmin) with hb
  have ha0 : 0 < a := mul_pos hφ (by linarith)
  have hab : a ≤ b := mul_le_mul_of_nonneg_left (by linarith) hφ.le
  have hs : 0 < a + b := by linarith
  refine ⟨2 / (a + b), by positivity, fun x t => ?_⟩
  have hrate : rateOf rmax rmin * (a + b) = b - a := by
    have hd : (2 : ℝ) - rmax - rmin ≠ 0 := by
      have : (0 : ℝ) < 2 - rmax - rmin := by linarith
      exact this.ne'
    unfold rateOf
    rw [ha, hb]
    field_simp
    ring
  refine sqNorm_err_iterate (fun k hk => ?_) x t
  have hmem : r (addOrderOf k) ∈ DivSet n := (mem_divSet_iff _).mpr ⟨k, hk, rfl⟩
  have hlo : a ≤ lapEig n k := mul_le_mul_of_nonneg_left (by linarith [hmax.2 hmem]) hφ.le
  have hhi : lapEig n k ≤ b := mul_le_mul_of_nonneg_left (by linarith [hmin.2 hmem]) hφ.le
  exact contraction_of_opt_step hs (by field_simp) hrate hlo hhi

/-- Every `n ≥ 2` has an optimal rate. -/
theorem exists_isRate {m : ℕ} (hm : 2 ≤ m) : ∃ ρ : ℝ, IsRate m ρ := by
  by_cases hpp : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : k = 1 := by omega
      subst this
      rw [pow_one]
      exact ⟨0, isRate_prime hp⟩
    · exact ⟨_, isRate_prime_pow hp hk2⟩
  · obtain ⟨q, hts⟩ := exists_twoSmallest hm hpp
    exact ⟨_, isRate_of_twoSmallest hm hts⟩

theorem isRate_nonneg {m : ℕ} {ρ : ℝ} (h : IsRate m ρ) : 0 ≤ ρ := by
  obtain ⟨rmax, rmin, hmax, hmin, rfl⟩ := h
  obtain ⟨M, _, hM, hrM⟩ := hmax.1
  have hrmax : rmax ≤ 1 / 2 := hrM ▸ r_le_half_of_one_lt hM
  have hle : rmin ≤ rmax := hmin.2 hmax.1
  unfold rateOf
  apply div_nonneg <;> linarith

/-- **Corollary 4.5, dynamical form.**  On every unitary Cayley graph `X_n`, `n ≥ 2`, the
optimally tuned iteration satisfies `‖x(t) - x̄ 1‖ ≤ (3/5)^t ‖x(0) - x̄ 1‖`. -/
theorem consensus_three_fifths (hn : 2 ≤ n) :
    ∃ ε > 0, ∀ (x : ZMod n → ℝ) (t : ℕ),
      sqNorm (err ((step ε)^[t] x)) ≤ (((3 : ℝ) / 5) ^ 2) ^ t * sqNorm (err x) := by
  obtain ⟨ρ, hρ⟩ := exists_isRate hn
  obtain ⟨ε, hε, hbound⟩ := consensus_of_isRate hρ
  refine ⟨ε, hε, fun x t => (hbound x t).trans ?_⟩
  have h0 := isRate_nonneg hρ
  have h1 := (rate_le_and_eq_iff hn hρ).1
  refine mul_le_mul_of_nonneg_right ?_ (sqNorm_nonneg _)
  exact pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ h0 h1 2) t

/-- **Corollary 4.5, iteration count.**  `(3/5)^t ≤ δ` as soon as `t ≥ log(1/δ)/log(5/3)`. -/
theorem three_fifths_pow_le {δ : ℝ} (hδ : 0 < δ) {t : ℕ}
    (ht : Real.log (1 / δ) / Real.log (5 / 3) ≤ t) : ((3 : ℝ) / 5) ^ t ≤ δ := by
  have hl : 0 < Real.log (5 / 3) := Real.log_pos (by norm_num)
  have h1 : Real.log (1 / δ) ≤ t * Real.log (5 / 3) := by
    rw [div_le_iff₀ hl] at ht
    exact ht
  have h2 : Real.log (((3 : ℝ) / 5) ^ t) = -(t * Real.log (5 / 3)) := by
    rw [Real.log_pow]
    have : Real.log ((3 : ℝ) / 5) = -Real.log (5 / 3) := by
      rw [← Real.log_inv]
      norm_num
    rw [this]
    ring
  have h3 : Real.log (((3 : ℝ) / 5) ^ t) ≤ Real.log δ := by
    rw [h2]
    have : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
    linarith
  exact (Real.log_le_log_iff (by positivity) hδ).mp h3

/-- **Corollary 4.5, numerical instance.**  `28` iterations reduce the error by `10⁶`. -/
theorem twentyeight_iterations : ((3 : ℝ) / 5) ^ 28 ≤ 1 / 10 ^ 6 := by
  norm_num

/-! ### The optimal step (4.6) -/

/-- **Theorem 4.3, the optimal step when `ω(n) ≥ 2`.** -/
theorem opt_step_two_primes {φ p q : ℝ} (hφ : 0 < φ) (hp : 2 ≤ p) (hq : 3 ≤ q) :
    2 / (φ * (1 - 1 / ((p - 1) * (q - 1))) + φ * (p / (p - 1)))
      = 2 * (p - 1) * (q - 1) / (φ * (2 * (p - 1) * (q - 1) + q - 2)) := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : q - 1 ≠ 0 := by linarith
  have hD : 0 < 2 * (p - 1) * (q - 1) + q - 2 := rate_denominator_pos hp hq
  have hS : φ * (1 - 1 / ((p - 1) * (q - 1))) + φ * (p / (p - 1))
      = φ * (2 * (p - 1) * (q - 1) + q - 2) / ((p - 1) * (q - 1)) := by
    field_simp
    ring
  rw [hS]
  field_simp

/-- **Theorem 4.3, the optimal step for `n = p^a`, `a ≥ 2`.** -/
theorem opt_step_prime_pow {φ p : ℝ} (hφ : 0 < φ) (hp : 2 ≤ p) :
    2 / (φ + φ * (p / (p - 1))) = 2 * (p - 1) / ((2 * p - 1) * φ) := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : 2 * p - 1 ≠ 0 := by linarith
  have hS : φ + φ * (p / (p - 1)) = (2 * p - 1) * φ / (p - 1) := by
    field_simp
    ring
  rw [hS]
  field_simp

/-- **Theorem 4.3, the optimal step for `n` prime.** -/
theorem opt_step_prime {m : ℝ} (hm : 0 < m) : 2 / (m + m) = 1 / m := by
  field_simp
  ring

/-! ### Proposition 4.7: the natural step `ε = 1/φ(n)` -/

/-- **Proposition 4.7, contraction factor.**  The non-trivial eigenvalues `r(ord k)` of
`I - L/φ(n) = A/φ(n)` have largest modulus exactly `1/(p-1)`. -/
theorem natural_step_factor (hn : 1 < n) :
    IsGreatest {y : ℝ | ∃ k : ZMod n, k ≠ 0 ∧ |r (addOrderOf k)| = y}
      (1 / ((n.minFac : ℝ) - 1)) := by
  have hn1 : n ≠ 1 := by omega
  have hp := Nat.minFac_prime hn1
  have hp1 : (0 : ℝ) < (n.minFac : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
    linarith
  refine ⟨⟨((n / n.minFac : ℕ) : ZMod n), natCast_div_ne_zero (Nat.minFac_dvd n) hp.one_lt, ?_⟩, ?_⟩
  · rw [addOrderOf_natCast_div (Nat.minFac_dvd n), r_minFac hn1, abs_div, abs_neg, abs_one,
      abs_of_pos hp1]
  · rintro y ⟨k, hk, rfl⟩
    exact abs_r_le_of_dvd (one_lt_addOrderOf hk) (addOrderOf_dvd_self k)

omit [NeZero n] in
/-- **Proposition 4.7, convergence criterion.**  The factor `1/(p-1)` is `< 1` iff `n` is odd. -/
theorem natural_step_lt_one_iff (hn : 1 < n) :
    1 / ((n.minFac : ℝ) - 1) < 1 ↔ Odd n := by
  have hp := Nat.minFac_prime (show n ≠ 1 by omega)
  have hp1 : (0 : ℝ) < (n.minFac : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
    linarith
  rw [div_lt_one hp1, ← Nat.not_even_iff_odd, even_iff_two_dvd, ← Nat.minFac_eq_two_iff]
  constructor
  · intro h h2
    rw [h2] at h
    norm_num at h
  · intro h
    have h3 : 3 ≤ n.minFac := by
      have := hp.two_le
      omega
    have : (3 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast h3
    linarith

/-- The alternating vector `v_j = (-1)^j` on `ℤ/n` for even `n`. -/
noncomputable def alternating (n : ℕ) : ZMod n → ℝ := fun j => (-1) ^ j.val

theorem alternating_add (h2 : 2 ∣ n) (i j : ZMod n) :
    alternating n (i + j) = alternating n i * alternating n j := by
  have key : ∀ m : ℕ, ((-1 : ℝ)) ^ (m % n) = (-1) ^ m := by
    intro m
    obtain ⟨c, hc⟩ := h2
    have e := Nat.mod_add_div m n
    have hev : Even n := ⟨c, by omega⟩
    calc ((-1 : ℝ)) ^ (m % n) = (-1) ^ (m % n) * ((-1) ^ n) ^ (m / n) := by
          rw [Even.neg_one_pow hev, one_pow, mul_one]
      _ = (-1) ^ m := by rw [← pow_mul, ← pow_add, e]
  unfold alternating
  rw [ZMod.val_add, key, pow_add]

omit [NeZero n] in
theorem alternating_unit (h2 : 2 ∣ n) (u : (ZMod n)ˣ) : alternating n u = -1 := by
  unfold alternating
  have hodd : ¬ 2 ∣ (u : ZMod n).val := by
    intro h
    have hc := ZMod.val_coe_unit_coprime u
    have := Nat.dvd_gcd h h2
    rw [hc] at this
    omega
  rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]

/-- **Proposition 4.7, non-convergence for even `n`.**  The alternating vector is a non-zero
sum-zero vector that the natural step maps to its negative, so its error never decays. -/
theorem natural_step_even (h2 : 2 ∣ n) :
    ∑ j, alternating n j = 0 ∧ alternating n ≠ 0 ∧
      step (1 / (Nat.totient n : ℝ)) (alternating n) = fun j => -alternating n j := by
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  have hn2 : 1 < n := by
    obtain ⟨c, hc⟩ := h2
    have := NeZero.ne n
    omega
  have h1 : ∀ i : ZMod n, alternating n (i + 1) = -alternating n i := by
    intro i
    have hu : IsUnit (1 : ZMod n) := isUnit_one
    rw [alternating_add h2]
    have := alternating_unit h2 hu.unit
    rw [IsUnit.unit_spec] at this
    rw [this]
    ring
  refine ⟨?_, ?_, ?_⟩
  · have := Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) (alternating n)
    simp only [Equiv.coe_addRight, h1, sum_neg_distrib] at this
    linarith
  · intro h
    have := congrFun h 0
    simp [alternating] at this
  · funext j
    unfold step lapR
    have : ∀ u : (ZMod n)ˣ, alternating n (j + u) = -alternating n j := by
      intro u
      rw [alternating_add h2, alternating_unit h2]
      ring
    rw [sum_congr rfl fun u _ => this u, sum_const, card_univ, ZMod.card_units_eq_totient,
      nsmul_eq_mul]
    field_simp
    ring

/-! ### Remark 4.8: continuous time -/

/-- **Remark 4.8.**  For a solution of `ẋ = -L x` on `X_n` and any `a` with `a ≤ λ(k)` for all
`k ≠ 0`, `‖x(t) - x̄ 1‖² ≤ e^{-2at} ‖x(0) - x̄ 1‖²` for `t ≥ 0`. -/
theorem continuous_consensus {a : ℝ} (ha : ∀ k : ZMod n, k ≠ 0 → a ≤ lapEig n k)
    (x : ℝ → ZMod n → ℝ) (hx : ∀ t, HasDerivAt x (fun j => -lapR (x t) j) t) {t : ℝ}
    (ht : 0 ≤ t) :
    sqNorm (err (x t)) ≤ Real.exp (-2 * a * t) * sqNorm (err (x 0)) := by
  have hcomp : ∀ s (j : ZMod n), HasDerivAt (fun s => x s j) (-lapR (x s) j) s :=
    fun s j => (hasDerivAt_pi.mp (hx s)) j
  -- the sum, hence the average, is conserved
  have hsum : ∀ s, HasDerivAt (fun s => ∑ j, x s j) 0 s := by
    intro s
    have := HasDerivAt.fun_sum (u := univ) fun j _ => hcomp s j
    simpa [sum_neg_distrib, sum_lapR] using this
  have hconst : ∀ s, avg (x s) = avg (x 0) := by
    intro s
    have hd : Differentiable ℝ (fun s => ∑ j, x s j) := fun s => (hsum s).differentiableAt
    have := is_const_of_deriv_eq_zero hd (fun s => (hsum s).deriv) s 0
    unfold avg
    rw [this]
  set c := avg (x 0) with hc
  set g : ℝ → ℝ := fun s => ∑ j, (x s j - c) ^ 2 with hg
  have hgerr : ∀ s, g s = sqNorm (err (x s)) := by
    intro s
    unfold sqNorm err
    rw [hconst s]
  have hgd : ∀ s, HasDerivAt g (-2 * ∑ j, lapR (fun j => x s j - c) j * (x s j - c)) s := by
    intro s
    have := HasDerivAt.fun_sum (u := univ) fun j _ => ((hcomp s j).sub_const c).pow 2
    convert this using 1
    rw [mul_sum, lapR_sub_const]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hupper : ∀ k : ZMod n, k ≠ 0 → lapEig n k ≤ ∑ k', |lapEig n k'| := fun k _ =>
    (le_abs_self _).trans (single_le_sum (f := fun k' => |lapEig n k'|)
      (fun _ _ => abs_nonneg _) (mem_univ k))
  have hq : ∀ s, a * g s ≤ ∑ j, lapR (fun j => x s j - c) j * (x s j - c) := by
    intro s
    have hz : ∑ j, (x s j - c) = 0 := by
      have := sum_err (x s)
      unfold err at this
      rw [hconst s] at this
      exact this
    exact (quadForm_bounds (fun j => x s j - c) hz ha hupper).1
  set h : ℝ → ℝ := fun s => g s * Real.exp (2 * a * s) with hh
  have hhd : ∀ s, HasDerivAt h ((-2 * ∑ j, lapR (fun j => x s j - c) j * (x s j - c))
      * Real.exp (2 * a * s) + g s * (Real.exp (2 * a * s) * (2 * a))) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (2 * a * s)) (Real.exp (2 * a * s) * (2 * a)) s := by
      have := ((hasDerivAt_id s).const_mul (2 * a)).exp
      simpa using this
    exact (hgd s).mul he
  have hanti : Antitone h := by
    refine antitone_of_hasDerivAt_nonpos hhd fun s => ?_
    have hpos := Real.exp_pos (2 * a * s)
    have hle := mul_le_mul_of_nonneg_left (hq s) hpos.le
    have e : (-2 * ∑ j, lapR (fun j => x s j - c) j * (x s j - c)) * Real.exp (2 * a * s)
        + g s * (Real.exp (2 * a * s) * (2 * a))
        = 2 * (Real.exp (2 * a * s) * (a * g s)
          - Real.exp (2 * a * s) * ∑ j, lapR (fun j => x s j - c) j * (x s j - c)) := by ring
    rw [e]
    simp only [Pi.zero_apply]
    linarith
  have h0 := hanti ht
  simp only [hh, mul_zero, Real.exp_zero, mul_one] at h0
  rw [← hgerr t, ← hgerr 0]
  have hexp : Real.exp (-2 * a * t) * Real.exp (2 * a * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc g t = g t * Real.exp (2 * a * t) * Real.exp (-2 * a * t) := by
          rw [mul_assoc, mul_comm (Real.exp (2 * a * t)), hexp, mul_one]
    _ ≤ g 0 * Real.exp (-2 * a * t) :=
        mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le
    _ = Real.exp (-2 * a * t) * g 0 := by ring

end ArithmeticDynamics

/-! ════════════════════════ Part 13: Density ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XIII: densities — the mean of a periodic sequence, and counting residues with
prescribed reductions modulo a set of primes (Chinese remainder theorem).
-/

namespace ArithmeticDynamics

open Finset Filter Topology

theorem periodic_shift (g : ℕ → ℝ) {Q : ℕ} (hg : ∀ m, g (m + Q) = g m) (k x : ℕ) :
    g (k * Q + x) = g x := by
  induction k with
  | zero => simp
  | succ k ihk =>
    have : (k + 1) * Q + x = (k * Q + x) + Q := by ring
    rw [this, hg, ihk]

/-- Partial sums of a periodic sequence over whole periods. -/
theorem sum_range_mul_period (g : ℕ → ℝ) {Q : ℕ} (hg : ∀ m, g (m + Q) = g m) (k : ℕ) :
    ∑ m ∈ range (k * Q), g m = k * ∑ m ∈ range Q, g m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    simp_rw [periodic_shift g hg]
    push_cast
    ring

/-- **Mean of a periodic sequence.**  If `g` has period `Q > 0`, then
`(1/N) ∑_{m<N} g(m) → (1/Q) ∑_{m<Q} g(m)`. -/
theorem tendsto_avg_periodic (g : ℕ → ℝ) {Q : ℕ} (hQ : 0 < Q) (hg : ∀ m, g (m + Q) = g m) :
    Tendsto (fun N : ℕ => (∑ m ∈ range N, g m) / N) atTop
      (𝓝 ((∑ m ∈ range Q, g m) / Q)) := by
  set S := ∑ m ∈ range Q, g m with hS
  set B := ∑ m ∈ range Q, |g m| with hB
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have key : ∀ N : ℕ, |∑ m ∈ range N, g m - N * (S / Q)| ≤ B + |S| := by
    intro N
    have hN := Nat.div_add_mod N Q
    set k := N / Q
    set r := N % Q
    have hr : r < Q := Nat.mod_lt N hQ
    have hsplit : ∑ m ∈ range N, g m = k * S + ∑ m ∈ range r, g m := by
      rw [← hN, mul_comm Q k, sum_range_add, sum_range_mul_period g hg]
      simp_rw [periodic_shift g hg]
      rw [hS]
    have hNr : (N : ℝ) = k * Q + r := by
      have : ((Q * k + r : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hN
      push_cast at this
      linarith
    have hrem : |∑ m ∈ range r, g m| ≤ B := by
      calc |∑ m ∈ range r, g m| ≤ ∑ m ∈ range r, |g m| := abs_sum_le_sum_abs _ _
        _ ≤ B := sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hr.le)
            (fun _ _ _ => abs_nonneg _)
    have hfrac : |(r : ℝ) * (S / Q)| ≤ |S| := by
      rw [abs_mul, abs_div, abs_of_pos hQr, Nat.abs_cast]
      have : (r : ℝ) / Q ≤ 1 := by
        rw [div_le_one hQr]
        exact_mod_cast hr.le
      calc (r : ℝ) * (|S| / Q) = (r / Q) * |S| := by ring
        _ ≤ 1 * |S| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = |S| := one_mul _
    have e : ∑ m ∈ range N, g m - N * (S / Q) = ∑ m ∈ range r, g m - r * (S / Q) := by
      rw [hsplit, hNr]
      field_simp
      ring
    rw [e]
    calc |∑ m ∈ range r, g m - r * (S / Q)| ≤ |∑ m ∈ range r, g m| + |(r : ℝ) * (S / Q)| :=
          abs_sub _ _
      _ ≤ B + |S| := add_le_add hrem hfrac
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (B + |S|))
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.norm_eq_abs]
  have : (∑ m ∈ range N, g m) / N - S / Q = (∑ m ∈ range N, g m - N * (S / Q)) / N := by
    field_simp
  rw [this, abs_div, abs_of_pos hNr]
  exact div_le_div_of_nonneg_right (key N) hNr.le

/-! ### Counting with the Chinese remainder theorem -/

section CRT

variable (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime)

/-- The product of the primes in `P`, indexed by the subtype. -/
abbrev primorialOf : ℕ := ∏ i : P, (i : ℕ)

include hP in
theorem primorialOf_pos : 0 < primorialOf P :=
  Finset.prod_pos fun i _ => (hP i i.2).pos

theorem dvd_primorialOf {ℓ : ℕ} (hℓ : ℓ ∈ P) : ℓ ∣ primorialOf P := by
  unfold primorialOf
  exact Finset.dvd_prod_of_mem (fun i : P => (i : ℕ)) (mem_univ ⟨ℓ, hℓ⟩)

include hP in
theorem pairwise_coprime_primes :
    Pairwise (Function.onFun Nat.Coprime (fun i : P => (i : ℕ))) := by
  intro i j hij
  exact (Nat.coprime_primes (hP i i.2) (hP j j.2)).mpr (fun h => hij (Subtype.ext h))

include hP in
/-- **Counting residues by their reductions.**  The number of `m < ∏ P` whose reduction modulo
each `ℓ ∈ P` lies in a prescribed set `T ℓ` is `∏_ℓ |T ℓ|`. -/
theorem card_crt (T : ∀ i : P, Finset (ZMod (i : ℕ))) :
    #((range (primorialOf P)).filter (fun m => ∀ i : P, ((m : ℕ) : ZMod (i : ℕ)) ∈ T i))
      = ∏ i : P, #(T i) := by
  classical
  have hQ : NeZero (primorialOf P) := ⟨(primorialOf_pos P hP).ne'⟩
  set e := ZMod.prodEquivPi (fun i : P => (i : ℕ)) (pairwise_coprime_primes P hP) with he
  have happ : ∀ (x : ZMod (primorialOf P)) (i : P), e x i = (ZMod.cast x : ZMod (i : ℕ)) :=
    fun x i => by rw [he]; exact (ZMod.prodEquivPi_apply _ _ x i).trans (ZMod.castHom_apply _)
  -- reindex `range Q` by `ZMod Q`
  have h1 : #((range (primorialOf P)).filter (fun m => ∀ i : P, ((m : ℕ) : ZMod (i : ℕ)) ∈ T i))
      = #(univ.filter (fun x : ZMod (primorialOf P) => ∀ i : P, e x i ∈ T i)) := by
    refine card_bij (fun m _ => (m : ZMod (primorialOf P))) ?_ ?_ ?_
    · intro m hm
      simp only [mem_filter, mem_range] at hm
      simp only [mem_filter, mem_univ, true_and]
      intro i
      rw [happ, ZMod.cast_natCast (dvd_primorialOf P i.2)]
      exact hm.2 i
    · intro a ha b hb hab
      simp only [mem_filter, mem_range] at ha hb
      have := congrArg ZMod.val hab
      rwa [ZMod.val_natCast_of_lt ha.1, ZMod.val_natCast_of_lt hb.1] at this
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
      simp only [mem_filter, mem_range]
      refine ⟨ZMod.val_lt x, fun i => ?_⟩
      have := hx i
      rwa [happ, ← ZMod.natCast_val] at this
  -- transport along the CRT equivalence
  have h2 : #(univ.filter (fun x : ZMod (primorialOf P) => ∀ i : P, e x i ∈ T i))
      = #(Fintype.piFinset T) := by
    refine card_bij (fun x _ => e x) ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      exact Fintype.mem_piFinset.mpr hx
    · intro a _ b _ hab
      exact e.injective hab
    · intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [mem_filter]
      refine ⟨mem_univ _, fun i => ?_⟩
      rw [e.apply_symm_apply]
      exact Fintype.mem_piFinset.mp hy i
  rw [h1, h2, Fintype.card_piFinset]

end CRT

end ArithmeticDynamics

/-! ════════════════════════ Part 14: MeanValue ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XIV: the mean value of the optimal consensus rate (Proposition 4.9).
-/

namespace ArithmeticDynamics

open Finset Filter Topology
open scoped Classical

/-! ### The rate as a function of `n` -/

/-- The optimal consensus rate `ρ*(X_m)` as a function of `m` (`0` for `m < 2`). -/
noncomputable def rhoStar (m : ℕ) : ℝ :=
  if h : 2 ≤ m then Classical.choose (exists_isRate h) else 0

theorem isRate_rhoStar {m : ℕ} (hm : 2 ≤ m) : IsRate m (rhoStar m) := by
  unfold rhoStar
  rw [dif_pos hm]
  exact Classical.choose_spec (exists_isRate hm)

theorem rhoStar_nonneg (m : ℕ) : 0 ≤ rhoStar m := by
  by_cases hm : 2 ≤ m
  · exact isRate_nonneg (isRate_rhoStar hm)
  · simp [rhoStar, hm]

theorem rhoStar_le (m : ℕ) : rhoStar m ≤ 3 / 5 := by
  by_cases hm : 2 ≤ m
  · exact (rate_le_and_eq_iff hm (isRate_rhoStar hm)).1
  · simp only [rhoStar, hm, dite_false]
    norm_num

/-- `q / (2(p-1)(q-1) + q - 2)`, the rate on integers whose two smallest primes are `p < q`. -/
noncomputable def rateVal (p q : ℕ) : ℝ := (q : ℝ) / (2 * ((p : ℝ) - 1) * ((q : ℝ) - 1) + q - 2)

/-- The natural density `(1/(pq)) ∏_{ℓ < q, ℓ ≠ p} (1 - 1/ℓ)` of the integers whose two smallest
prime divisors are `p < q`. -/
noncomputable def dens (p q : ℕ) : ℝ :=
  1 / ((p : ℝ) * q) * ∏ ℓ ∈ (range q).filter (fun ℓ => ℓ.Prime ∧ ℓ ≠ p), (1 - 1 / (ℓ : ℝ))

/-- The terms of the series (4.7). -/
noncomputable def pairWeight (pq : ℕ × ℕ) : ℝ :=
  if pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 then rateVal pq.1 pq.2 * dens pq.1 pq.2 else 0

theorem rateVal_nonneg_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    0 ≤ rateVal p q ∧ rateVal p q ≤ 3 / 5 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq3 : (3 : ℝ) ≤ q := by
    have : 3 ≤ q := by have := hp.two_le; omega
    exact_mod_cast this
  have hD := rate_denominator_pos hp2 hq3
  unfold rateVal
  refine ⟨div_nonneg (by linarith) hD.le, ?_⟩
  rw [div_le_iff₀ hD]
  have := universal_bound hp2 hq3
  linarith

theorem dens_nonneg (p q : ℕ) : 0 ≤ dens p q := by
  unfold dens
  refine mul_nonneg (by positivity) (prod_nonneg fun ℓ hℓ => ?_)
  have hℓ' := (mem_filter.mp hℓ).2.1
  have : (1 : ℝ) / ℓ ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hℓ'.pos)]
    exact_mod_cast hℓ'.one_lt.le
  linarith

theorem pairWeight_nonneg (pq : ℕ × ℕ) : 0 ≤ pairWeight pq := by
  unfold pairWeight
  split_ifs with h
  · exact mul_nonneg (rateVal_nonneg_le h.1 h.2.1 h.2.2).1 (dens_nonneg _ _)
  · exact le_rfl

/-! ### The sets `A_{p,q}` -/

/-- `m ∈ A_{p,q}`: `p, q ∣ m` and no prime `ℓ < q` other than `p` divides `m`. -/
def InA (p q m : ℕ) : Prop := p ∣ m ∧ q ∣ m ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ < q → ℓ ≠ p → ¬ ℓ ∣ m

theorem inA_iff {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    InA p q m ↔ TwoSmallest m p q := by
  constructor
  · rintro ⟨hpm, hqm, h⟩
    refine ⟨hp, hq, hpm, hqm, hpq, fun ℓ hℓ hℓm => ?_, fun ℓ hℓ hℓm hℓp => ?_⟩
    · by_contra hlt
      exact h ℓ hℓ (by omega) (by omega) hℓm
    · by_contra hlt
      exact h ℓ hℓ (by omega) hℓp hℓm
  · intro h
    refine ⟨h.hpn, h.hqn, fun ℓ hℓ hlt hne hdvd => ?_⟩
    have := h.second ℓ hℓ hdvd hne
    omega

theorem twoSmallest_unique {m p q p' q' : ℕ} (h : TwoSmallest m p q) (h' : TwoSmallest m p' q') :
    p = p' ∧ q = q' := by
  have hpp : p = p' := le_antisymm (h.least p' h'.hp h'.hpn) (h'.least p h.hp h.hpn)
  refine ⟨hpp, le_antisymm ?_ ?_⟩
  · exact h.second q' h'.hq h'.hqn (by have := h'.hlt; omega)
  · exact h'.second q h.hq h.hqn (by have := h.hlt; omega)

theorem rhoStar_eq {m p q : ℕ} (hm : 2 ≤ m) (h : TwoSmallest m p q) : rhoStar m = rateVal p q := by
  have hpm : p = m.minFac :=
    le_antisymm (h.least _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd m))
      (Nat.minFac_le_of_dvd h.hp.two_le h.hpn)
  have h' : TwoSmallest m m.minFac q := hpm ▸ h
  have := (isRate_rhoStar hm).unique (isRate_of_twoSmallest hm h')
  rw [this, rateVal, ← hpm]

/-! ### Truncation at the primes up to `y` -/

/-- The primes `≤ y`. -/
def primesUpTo (y : ℕ) : Finset ℕ := (range (y + 1)).filter Nat.Prime

/-- Pairs of primes `p < q ≤ y`. -/
def pairsUpTo (y : ℕ) : Finset (ℕ × ℕ) :=
  ((range (y + 1)) ×ˢ (range (y + 1))).filter (fun pq => pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2)

theorem mem_pairsUpTo {y : ℕ} {pq : ℕ × ℕ} :
    pq ∈ pairsUpTo y ↔ pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 ∧ pq.2 ≤ y := by
  unfold pairsUpTo
  simp only [mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨_, h2⟩, h3, h4, h5⟩
    exact ⟨h3, h4, h5, by omega⟩
  · rintro ⟨h3, h4, h5, h6⟩
    exact ⟨⟨by omega, by omega⟩, h3, h4, h5⟩

theorem primes_mem {y ℓ : ℕ} (hℓ : ℓ.Prime) (hy : ℓ ≤ y) : ℓ ∈ primesUpTo y := by
  unfold primesUpTo
  simp only [mem_filter, mem_range]
  exact ⟨by omega, hℓ⟩

theorem primesUpTo_prime {y : ℕ} : ∀ ℓ ∈ primesUpTo y, ℓ.Prime := fun ℓ h =>
  (mem_filter.mp h).2

/-- `m` has at most one prime divisor `≤ y` (the exceptional set `E_y`). -/
def InE (y m : ℕ) : Prop := ∀ pq ∈ pairsUpTo y, ¬ InA pq.1 pq.2 m

/-- The truncated rate: the value of `ρ*` determined by the primes `≤ y`. -/
noncomputable def fy (y m : ℕ) : ℝ :=
  ∑ pq ∈ pairsUpTo y, if InA pq.1 pq.2 m then rateVal pq.1 pq.2 else 0

theorem fy_eq_of_mem {y m : ℕ} {pq : ℕ × ℕ} (hmem : pq ∈ pairsUpTo y) (hA : InA pq.1 pq.2 m) :
    fy y m = rateVal pq.1 pq.2 := by
  unfold fy
  rw [sum_eq_single pq]
  · simp [hA]
  · intro pq' hmem' hne
    rw [if_neg]
    intro hA'
    obtain ⟨h1, h2, h3, _⟩ := mem_pairsUpTo.mp hmem
    obtain ⟨h1', h2', h3', _⟩ := mem_pairsUpTo.mp hmem'
    obtain ⟨e1, e2⟩ := twoSmallest_unique ((inA_iff h1 h2 h3).mp hA) ((inA_iff h1' h2' h3').mp hA')
    exact hne (Prod.ext e1.symm e2.symm)
  · intro h
    exact absurd hmem h

theorem fy_eq_zero {y m : ℕ} (hE : InE y m) : fy y m = 0 := by
  unfold fy
  exact sum_eq_zero fun pq hpq => by rw [if_neg (hE pq hpq)]

theorem fy_nonneg_le (y m : ℕ) : 0 ≤ fy y m ∧ fy y m ≤ 3 / 5 := by
  by_cases hE : InE y m
  · rw [fy_eq_zero hE]
    norm_num
  · unfold InE at hE
    push_neg at hE
    obtain ⟨pq, hmem, hA⟩ := hE
    rw [fy_eq_of_mem hmem hA]
    obtain ⟨h1, h2, h3, _⟩ := mem_pairsUpTo.mp hmem
    exact rateVal_nonneg_le h1 h2 h3

/-- The truncation error is controlled by the exceptional set and the two points `0, 1`. -/
theorem abs_rhoStar_sub_fy (y m : ℕ) :
    |rhoStar m - fy y m| ≤ (if InE y m then 1 else 0) + (if m < 2 then 1 else 0) := by
  have h1 := rhoStar_nonneg m
  have h2 := rhoStar_le m
  obtain ⟨h3, h4⟩ := fy_nonneg_le y m
  have hb : |rhoStar m - fy y m| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  by_cases hE : InE y m
  · rw [if_pos hE]
    split_ifs <;> linarith
  · by_cases hm : m < 2
    · rw [if_pos hm]
      split_ifs <;> linarith
    · rw [if_neg hE, if_neg hm]
      unfold InE at hE
      push_neg at hE
      obtain ⟨pq, hmem, hA⟩ := hE
      obtain ⟨h1, h2, h3, _⟩ := mem_pairsUpTo.mp hmem
      rw [fy_eq_of_mem hmem hA, rhoStar_eq (by omega) ((inA_iff h1 h2 h3).mp hA)]
      simp

/-! ### Periodicity modulo the primorial -/

theorem inA_add_period {y p q m Q : ℕ} (hpq : (p, q) ∈ pairsUpTo y)
    (hQ : ∀ ℓ, ℓ.Prime → ℓ ≤ y → ℓ ∣ Q) : InA p q (m + Q) ↔ InA p q m := by
  obtain ⟨hp, hq, hlt, hqy⟩ := mem_pairsUpTo.mp hpq
  have key : ∀ ℓ, ℓ.Prime → ℓ ≤ y → (ℓ ∣ m + Q ↔ ℓ ∣ m) := fun ℓ hℓ hy =>
    Nat.dvd_add_left (hQ ℓ hℓ hy)
  unfold InA
  simp only at hp hq
  rw [key p hp (by omega), key q hq hqy]
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, fun ℓ hℓ h1 h2 => by rw [← key ℓ hℓ (by omega)]; exact c ℓ hℓ h1 h2⟩
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, fun ℓ hℓ h1 h2 => by rw [key ℓ hℓ (by omega)]; exact c ℓ hℓ h1 h2⟩

/-- The primorial of the primes `≤ y`. -/
abbrev Qy (y : ℕ) : ℕ := primorialOf (primesUpTo y)

theorem Qy_pos (y : ℕ) : 0 < Qy y := primorialOf_pos _ (primesUpTo_prime)

theorem dvd_Qy {y ℓ : ℕ} (hℓ : ℓ.Prime) (hy : ℓ ≤ y) : ℓ ∣ Qy y :=
  dvd_primorialOf _ (primes_mem hℓ hy)

theorem fy_periodic (y m : ℕ) : fy y (m + Qy y) = fy y m := by
  unfold fy
  refine sum_congr rfl fun pq hpq => ?_
  have := inA_add_period (m := m) hpq (fun ℓ hℓ hy => dvd_Qy hℓ hy)
  simp only [this]

theorem inE_periodic (y m : ℕ) : InE y (m + Qy y) ↔ InE y m := by
  unfold InE
  constructor
  · intro h pq hpq hA
    exact h pq hpq ((inA_add_period hpq (fun ℓ hℓ hy => dvd_Qy hℓ hy)).mpr hA)
  · intro h pq hpq hA
    exact h pq hpq ((inA_add_period hpq (fun ℓ hℓ hy => dvd_Qy hℓ hy)).mp hA)

/-! ### Densities of `A_{p,q}` -/

theorem card_ne_zero_zmod {ℓ : ℕ} [NeZero ℓ] :
    #(univ.filter (fun x : ZMod ℓ => x ≠ 0)) = ℓ - 1 := by
  rw [filter_ne', card_erase_of_mem (mem_univ _), card_univ, ZMod.card]

theorem natCast_zmod_eq_zero_iff {ℓ m : ℕ} : ((m : ℕ) : ZMod ℓ) = 0 ↔ ℓ ∣ m :=
  ZMod.natCast_eq_zero_iff m ℓ

/-- **The density of `A_{p,q}`.**  For primes `p < q ≤ y`, the proportion of `m < Q_y` in
`A_{p,q}` is exactly `dens p q`. -/
theorem density_inA {y p q : ℕ} (hpq : (p, q) ∈ pairsUpTo y) :
    (#((range (Qy y)).filter (InA p q)) : ℝ) / (Qy y) = dens p q := by
  obtain ⟨hp, hq, hlt, hqy⟩ := mem_pairsUpTo.mp hpq
  simp only at hp hq hlt hqy
  set P := primesUpTo y with hP
  have hPp : ∀ i : P, NeZero (i : ℕ) := fun i => ⟨(primesUpTo_prime i i.2).ne_zero⟩
  let T : ∀ i : P, Finset (ZMod (i : ℕ)) := fun i =>
    haveI := hPp i
    if (i : ℕ) = p ∨ (i : ℕ) = q then {0}
    else if (i : ℕ) < q then univ.filter (fun x => x ≠ 0) else univ
  have hset : (range (Qy y)).filter (InA p q)
      = (range (primorialOf P)).filter (fun m => ∀ i : P, ((m : ℕ) : ZMod (i : ℕ)) ∈ T i) := by
    ext m
    simp only [mem_filter, mem_range]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨hpm, hqm, hno⟩ i
      haveI := hPp i
      simp only [T]
      split_ifs with h1 h2
      · rcases h1 with h1 | h1
        · rw [mem_singleton, natCast_zmod_eq_zero_iff, h1]; exact hpm
        · rw [mem_singleton, natCast_zmod_eq_zero_iff, h1]; exact hqm
      · rw [mem_filter]
        refine ⟨mem_univ _, fun h0 => hno i (primesUpTo_prime i i.2) h2 ?_
          (natCast_zmod_eq_zero_iff.mp h0)⟩
        intro h
        exact h1 (Or.inl h)
      · exact mem_univ _
    · intro h
      have hpP : p ∈ P := primes_mem hp (by omega)
      have hqP : q ∈ P := primes_mem hq hqy
      refine ⟨?_, ?_, fun ℓ hℓ hℓq hℓp hdvd => ?_⟩
      · have hh := h ⟨p, hpP⟩
        simp only [T, true_or, if_true, mem_singleton] at hh
        exact natCast_zmod_eq_zero_iff.mp hh
      · have hh := h ⟨q, hqP⟩
        simp only [T, or_true, if_true, mem_singleton] at hh
        exact natCast_zmod_eq_zero_iff.mp hh
      · have hℓP : ℓ ∈ P := primes_mem hℓ (by omega)
        have hh := h ⟨ℓ, hℓP⟩
        have hne : ¬ (ℓ = p ∨ ℓ = q) := by omega
        simp only [T, hne, if_false, hℓq, if_true, mem_filter, mem_univ, true_and] at hh
        exact hh (natCast_zmod_eq_zero_iff.mpr hdvd)
  have hcard : ∀ i : P, (#(T i) : ℝ) / (i : ℕ)
      = (if (i : ℕ) = p ∨ (i : ℕ) = q then 1 / ((i : ℕ) : ℝ)
          else if (i : ℕ) < q then 1 - 1 / ((i : ℕ) : ℝ) else 1) := by
    intro i
    haveI := hPp i
    have hi : (0 : ℝ) < ((i : ℕ) : ℝ) := by exact_mod_cast (primesUpTo_prime i i.2).pos
    simp only [T]
    split_ifs
    · simp
    · rw [card_ne_zero_zmod, Nat.cast_sub (primesUpTo_prime i i.2).one_le, Nat.cast_one]
      field_simp
    · rw [card_univ, ZMod.card]
      field_simp
  have hQcast : ((Qy y : ℕ) : ℝ) = ∏ i : P, ((i : ℕ) : ℝ) := by rw [← Nat.cast_prod]
  rw [hset, card_crt P primesUpTo_prime T, hQcast, Nat.cast_prod, ← prod_div_distrib]
  simp_rw [hcard]
  rw [prod_coe_sort P (fun ℓ => if ℓ = p ∨ ℓ = q then 1 / (ℓ : ℝ)
      else if ℓ < q then 1 - 1 / (ℓ : ℝ) else 1)]
  have hsplit : ∀ ℓ : ℕ, (if ℓ = p ∨ ℓ = q then 1 / (ℓ : ℝ) else if ℓ < q then 1 - 1 / (ℓ : ℝ) else 1)
      = (if ℓ = p ∨ ℓ = q then 1 / (ℓ : ℝ) else 1)
        * (if ¬ (ℓ = p ∨ ℓ = q) ∧ ℓ < q then 1 - 1 / (ℓ : ℝ) else 1) := by
    intro ℓ
    by_cases h1 : ℓ = p ∨ ℓ = q
    · simp [h1]
    · by_cases h2 : ℓ < q <;> simp [h1, h2]
  simp_rw [hsplit]
  rw [prod_mul_distrib, ← prod_filter, ← prod_filter]
  have e1 : P.filter (fun ℓ => ℓ = p ∨ ℓ = q) = {p, q} := by
    ext ℓ
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro (rfl | rfl)
      · exact ⟨primes_mem hp (by omega), Or.inl rfl⟩
      · exact ⟨primes_mem hq hqy, Or.inr rfl⟩
  have e2 : P.filter (fun ℓ => ¬ (ℓ = p ∨ ℓ = q) ∧ ℓ < q)
      = (range q).filter (fun ℓ => ℓ.Prime ∧ ℓ ≠ p) := by
    ext ℓ
    simp only [hP, primesUpTo, mem_filter, mem_range]
    constructor
    · rintro ⟨⟨_, h2⟩, h3, h4⟩
      exact ⟨h4, h2, fun h => h3 (Or.inl h)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by omega, h2⟩, by omega, h1⟩
  rw [e1, e2, prod_pair (by omega), dens]
  field_simp

/-- **Average of the truncated rate over a period.** -/
theorem avg_fy (y : ℕ) :
    (∑ m ∈ range (Qy y), fy y m) / (Qy y) = ∑ pq ∈ pairsUpTo y, pairWeight pq := by
  have hQ : (0 : ℝ) < Qy y := by exact_mod_cast Qy_pos y
  unfold fy
  rw [sum_comm, sum_div]
  refine sum_congr rfl fun pq hpq => ?_
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm, mul_div_assoc,
    density_inA (by simpa using hpq)]
  obtain ⟨h1, h2, h3, _⟩ := mem_pairsUpTo.mp hpq
  simp [pairWeight, h1, h2, h3]

theorem sum_pairsUpTo_le (y : ℕ) : ∑ pq ∈ pairsUpTo y, pairWeight pq ≤ 3 / 5 := by
  have hQ : (0 : ℝ) < Qy y := by exact_mod_cast Qy_pos y
  rw [← avg_fy, div_le_iff₀ hQ]
  calc ∑ m ∈ range (Qy y), fy y m ≤ ∑ m ∈ range (Qy y), (3 / 5 : ℝ) :=
        sum_le_sum fun m _ => (fy_nonneg_le y m).2
    _ = 3 / 5 * (Qy y) := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-! ### The exceptional set -/

theorem not_inE_of_two {y m a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a < b) (hby : b ≤ y)
    (ham : a ∣ m) (hbm : b ∣ m) : ¬ InE y m := by
  intro hE
  by_cases hm0 : m = 0
  · subst hm0
    have hb3 : 3 ≤ b := by have := ha.two_le; omega
    refine hE (2, 3) (mem_pairsUpTo.mpr ⟨Nat.prime_two, Nat.prime_three, by norm_num, by omega⟩) ?_
    refine ⟨dvd_zero _, dvd_zero _, fun ℓ hℓ h1 h2 _ => ?_⟩
    have := hℓ.two_le
    omega
  · have hm2 : 2 ≤ m := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) ham
      have := ha.two_le
      omega
    have hpp : ¬ IsPrimePow m := by
      intro hpp
      obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
      have h1 := (Nat.prime_dvd_prime_iff_eq ha hr).mp (ha.dvd_of_dvd_pow ham)
      have h2 := (Nat.prime_dvd_prime_iff_eq hb hr).mp (hb.dvd_of_dvd_pow hbm)
      omega
    obtain ⟨q, hts⟩ := exists_twoSmallest hm2 hpp
    have hpa : m.minFac ≤ a := hts.least a ha ham
    have hqb : q ≤ b := hts.second b hb hbm (by omega)
    have hmem : (m.minFac, q) ∈ pairsUpTo y :=
      mem_pairsUpTo.mpr ⟨hts.hp, hts.hq, hts.hlt, by omega⟩
    exact hE _ hmem ((inA_iff hts.hp hts.hq hts.hlt).mpr hts)

/-- Elements of `E_y`: no prime `≤ y` divides `m`, or exactly one does. -/
theorem inE_cases {y m : ℕ} (hE : InE y m) :
    (∀ ℓ ∈ primesUpTo y, ¬ ℓ ∣ m) ∨
      ∃ p ∈ primesUpTo y, ∀ ℓ ∈ primesUpTo y, (ℓ ∣ m ↔ ℓ = p) := by
  by_cases h : ∃ p ∈ primesUpTo y, p ∣ m
  · obtain ⟨p, hp, hpm⟩ := h
    refine Or.inr ⟨p, hp, fun ℓ hℓ => ⟨fun hℓm => ?_, fun h => h ▸ hpm⟩⟩
    by_contra hne
    have hpy : p ≤ y := by have := (mem_filter.mp hp).1; simp at this; omega
    have hℓy : ℓ ≤ y := by have := (mem_filter.mp hℓ).1; simp at this; omega
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact not_inE_of_two (primesUpTo_prime ℓ hℓ) (primesUpTo_prime p hp) hlt hpy hℓm hpm hE
    · exact not_inE_of_two (primesUpTo_prime p hp) (primesUpTo_prime ℓ hℓ) hlt hℓy hpm hℓm hE
  · push_neg at h
    exact Or.inl h

/-- **The exceptional set is small.**  Its proportion in a period is at most
`e^{-S}(1 + 2S)`, `S = ∑_{p ≤ y} 1/p`. -/
theorem density_inE_le (y : ℕ) :
    (#((range (Qy y)).filter (InE y)) : ℝ) / (Qy y)
      ≤ Real.exp (-∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ)) * (1 + 2 * ∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ)) := by
  set P := primesUpTo y with hP
  have hQ : (0 : ℝ) < Qy y := by exact_mod_cast Qy_pos y
  have hPp : ∀ i : P, NeZero (i : ℕ) := fun i => ⟨(primesUpTo_prime i i.2).ne_zero⟩
  let T0 : ∀ i : P, Finset (ZMod (i : ℕ)) := fun i =>
    haveI := hPp i
    univ.filter (fun x => x ≠ 0)
  let Tp : ℕ → ∀ i : P, Finset (ZMod (i : ℕ)) := fun p i =>
    haveI := hPp i
    if (i : ℕ) = p then {0} else univ.filter (fun x => x ≠ 0)
  set A0 := (range (primorialOf P)).filter (fun m => ∀ i : P, ((m : ℕ) : ZMod (i : ℕ)) ∈ T0 i)
  set Ap := fun p => (range (primorialOf P)).filter
    (fun m => ∀ i : P, ((m : ℕ) : ZMod (i : ℕ)) ∈ Tp p i)
  have hsub : (range (Qy y)).filter (InE y) ⊆ A0 ∪ P.biUnion Ap := by
    intro m hm
    obtain ⟨hmr, hE⟩ := mem_filter.mp hm
    rcases inE_cases hE with h0 | ⟨p, hp, hpm⟩
    · refine mem_union_left _ (mem_filter.mpr ⟨hmr, fun i => ?_⟩)
      haveI := hPp i
      simp only [T0, mem_filter, mem_univ, true_and, ne_eq, natCast_zmod_eq_zero_iff]
      exact h0 i i.2
    · refine mem_union_right _ (mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hmr, fun i => ?_⟩⟩)
      haveI := hPp i
      simp only [Tp]
      split_ifs with hip
      · rw [mem_singleton, natCast_zmod_eq_zero_iff]
        exact (hpm i i.2).mpr hip
      · simp only [mem_filter, mem_univ, true_and, ne_eq, natCast_zmod_eq_zero_iff]
        exact fun h => hip ((hpm i i.2).mp h)
  have hQcast : ((Qy y : ℕ) : ℝ) = ∏ i : P, ((i : ℕ) : ℝ) := by rw [← Nat.cast_prod]
  have hc0 : (#A0 : ℝ) / (Qy y) = ∏ ℓ ∈ P, (1 - 1 / (ℓ : ℝ)) := by
    rw [card_crt P primesUpTo_prime T0, hQcast, Nat.cast_prod, ← prod_div_distrib, ← prod_coe_sort P (fun ℓ => 1 - 1 / (ℓ : ℝ))]
    refine prod_congr rfl fun i _ => ?_
    haveI := hPp i
    simp only [T0]
    rw [card_ne_zero_zmod, Nat.cast_sub (primesUpTo_prime i i.2).one_le, Nat.cast_one]
    have hi : ((i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (primesUpTo_prime i i.2).ne_zero
    field_simp
  have hcp : ∀ p ∈ P, (#(Ap p) : ℝ) / (Qy y)
      = ∏ ℓ ∈ P, (if ℓ = p then 1 / (ℓ : ℝ) else 1 - 1 / (ℓ : ℝ)) := by
    intro p _
    rw [card_crt P primesUpTo_prime (Tp p), hQcast, Nat.cast_prod, ← prod_div_distrib,
      ← prod_coe_sort P (fun ℓ => if ℓ = p then 1 / (ℓ : ℝ) else 1 - 1 / (ℓ : ℝ))]
    refine prod_congr rfl fun i _ => ?_
    haveI := hPp i
    have hi : ((i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (primesUpTo_prime i i.2).ne_zero
    simp only [Tp]
    split_ifs
    · simp
    · rw [card_ne_zero_zmod, Nat.cast_sub (primesUpTo_prime i i.2).one_le, Nat.cast_one]
      field_simp
  set E := ∏ ℓ ∈ P, (1 - 1 / (ℓ : ℝ)) with hEdef
  set S := ∑ ℓ ∈ P, 1 / (ℓ : ℝ) with hSdef
  have hfac : ∀ ℓ ∈ P, 0 ≤ 1 - 1 / (ℓ : ℝ) := by
    intro ℓ hℓ
    have hℓ' := primesUpTo_prime ℓ hℓ
    have : (1 : ℝ) / ℓ ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hℓ'.pos)]
      exact_mod_cast hℓ'.one_lt.le
    linarith
  have hE0 : 0 ≤ E := prod_nonneg hfac
  have hEexp : E ≤ Real.exp (-S) := by
    rw [hSdef, ← sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀ (h0 := hfac) (h1 := fun ℓ _ => by
      have := Real.one_sub_le_exp_neg (1 / (ℓ : ℝ))
      simpa using this)
  have hterm : ∀ p ∈ P, ∏ ℓ ∈ P, (if ℓ = p then 1 / (ℓ : ℝ) else 1 - 1 / (ℓ : ℝ))
      ≤ 2 * (1 / (p : ℝ)) * E := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (primesUpTo_prime p hp).two_le
    rw [← mul_prod_erase P _ hp, hEdef, ← mul_prod_erase P _ hp]
    have hR : ∏ ℓ ∈ P.erase p, (if ℓ = p then 1 / (ℓ : ℝ) else 1 - 1 / (ℓ : ℝ))
        = ∏ ℓ ∈ P.erase p, (1 - 1 / (ℓ : ℝ)) :=
      prod_congr rfl fun ℓ hℓ => by rw [if_neg (ne_of_mem_erase hℓ)]
    rw [hR, if_pos rfl]
    have hR0 : 0 ≤ ∏ ℓ ∈ P.erase p, (1 - 1 / (ℓ : ℝ)) :=
      prod_nonneg fun ℓ hℓ => hfac ℓ (mem_of_mem_erase hℓ)
    have hk : 1 / (p : ℝ) ≤ 2 * (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) := by
      have h1 : 0 < 1 / (p : ℝ) := by positivity
      have h2 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      nlinarith
    calc 1 / (p : ℝ) * ∏ ℓ ∈ P.erase p, (1 - 1 / (ℓ : ℝ))
        ≤ 2 * (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) * ∏ ℓ ∈ P.erase p, (1 - 1 / (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_right hk hR0
      _ = 2 * (1 / (p : ℝ)) * ((1 - 1 / (p : ℝ)) * ∏ ℓ ∈ P.erase p, (1 - 1 / (ℓ : ℝ))) := by ring
  have hcount : (#((range (Qy y)).filter (InE y)) : ℝ)
      ≤ (#A0 : ℝ) + ∑ p ∈ P, (#(Ap p) : ℝ) := by
    have h1 := card_le_card hsub
    have h2 := card_union_le A0 (P.biUnion Ap)
    have h3 := card_biUnion_le (s := P) (t := Ap)
    have : #((range (Qy y)).filter (InE y)) ≤ #A0 + ∑ p ∈ P, #(Ap p) := by omega
    exact_mod_cast this
  calc (#((range (Qy y)).filter (InE y)) : ℝ) / (Qy y)
      ≤ ((#A0 : ℝ) + ∑ p ∈ P, (#(Ap p) : ℝ)) / (Qy y) :=
        div_le_div_of_nonneg_right hcount hQ.le
    _ = E + ∑ p ∈ P, (#(Ap p) : ℝ) / (Qy y) := by rw [add_div, sum_div, hc0]
    _ ≤ E + ∑ p ∈ P, 2 * (1 / (p : ℝ)) * E := by
        gcongr with p hp
        rw [hcp p hp]
        exact hterm p hp
    _ = E * (1 + 2 * S) := by rw [← sum_mul, ← mul_sum, hSdef]; ring
    _ ≤ Real.exp (-S) * (1 + 2 * S) := by
        have : 0 ≤ 1 + 2 * S := by
          have : 0 ≤ S := sum_nonneg fun ℓ _ => by positivity
          linarith
        exact mul_le_mul_of_nonneg_right hEexp this

/-- The sum of `1/p` over the primes `≤ y` tends to infinity. -/
theorem tendsto_sum_primes_inv :
    Tendsto (fun y : ℕ => ∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ)) atTop atTop := by
  set f : ℕ → ℝ := Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => Set.indicator_nonneg (fun _ _ => by positivity) _
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).mp not_summable_one_div_on_primes
  have h' := h.comp (tendsto_add_atTop_nat 1)
  refine h'.congr fun y => ?_
  simp only [Function.comp_apply, primesUpTo, sum_filter, hf, Set.indicator_apply,
    Set.mem_setOf_eq]

theorem tendsto_bound_zero :
    Tendsto (fun y : ℕ => Real.exp (-∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ))
      * (1 + 2 * ∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ))) atTop (𝓝 0) := by
  have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hB : Tendsto (fun x : ℝ => Real.exp (-x) * (1 + 2 * x)) atTop (𝓝 0) := by
    have := h0.add (h1.const_mul 2)
    simp only [pow_zero, one_mul, pow_one, mul_zero, add_zero] at this
    refine this.congr fun x => ?_
    ring
  exact hB.comp tendsto_sum_primes_inv

/-! ### Summability and the main theorem -/

/-- The grid `[0, y]²`. -/
def grid (y : ℕ) : Finset (ℕ × ℕ) := (range (y + 1)) ×ˢ (range (y + 1))

theorem sum_grid (y : ℕ) : ∑ pq ∈ grid y, pairWeight pq = ∑ pq ∈ pairsUpTo y, pairWeight pq := by
  unfold pairsUpTo grid
  rw [sum_filter]
  refine sum_congr rfl fun pq _ => ?_
  unfold pairWeight
  split_ifs <;> simp_all

theorem summable_pairWeight : Summable pairWeight := by
  refine summable_of_sum_le (c := 3 / 5) (fun pq => pairWeight_nonneg pq) fun u => ?_
  set y := u.sup (fun pq => pq.1 + pq.2)
  have hsub : u ⊆ grid y := by
    intro pq hpq
    have := le_sup (f := fun pq : ℕ × ℕ => pq.1 + pq.2) hpq
    simp only [grid, mem_product, mem_range]
    constructor <;> omega
  calc ∑ pq ∈ u, pairWeight pq ≤ ∑ pq ∈ grid y, pairWeight pq :=
        sum_le_sum_of_subset_of_nonneg hsub fun pq _ _ => pairWeight_nonneg pq
    _ = ∑ pq ∈ pairsUpTo y, pairWeight pq := sum_grid y
    _ ≤ 3 / 5 := sum_pairsUpTo_le y

/-- The mean value `ρ̄ = ∑_{p<q} (1/(pq)) ∏_{ℓ<q, ℓ≠p} (1 - 1/ℓ) · q/(2(p-1)(q-1)+q-2)`. -/
noncomputable def meanRate : ℝ := ∑' pq, pairWeight pq

theorem tendsto_partial_meanRate :
    Tendsto (fun y => ∑ pq ∈ pairsUpTo y, pairWeight pq) atTop (𝓝 meanRate) := by
  have hmono : Monotone grid := by
    intro a b hab
    exact product_subset_product (range_subset_range.mpr (by omega))
      (range_subset_range.mpr (by omega))
  have hcover : ∀ pq : ℕ × ℕ, ∃ y, pq ∈ grid y := fun pq =>
    ⟨pq.1 + pq.2, by simp only [grid, mem_product, mem_range]; constructor <;> omega⟩
  have := summable_pairWeight.hasSum.comp (tendsto_atTop_finset_of_monotone hmono hcover)
  exact this.congr fun y => sum_grid y

/-- **Proposition 4.9 (mean value of the optimal consensus rate).**  The series defining
`meanRate` converges, and `(1/N) ∑_{n<N} ρ*(X_n) → meanRate`. -/
theorem mean_value :
    Summable pairWeight ∧
      Tendsto (fun N : ℕ => (∑ m ∈ range N, rhoStar m) / N) atTop (𝓝 meanRate) := by
  refine ⟨summable_pairWeight, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose the truncation level `y`
  have hy1 := (Metric.tendsto_atTop.mp tendsto_bound_zero) (ε / 4) (by positivity)
  have hy2 := (Metric.tendsto_atTop.mp tendsto_partial_meanRate) (ε / 4) (by positivity)
  obtain ⟨y1, hy1⟩ := hy1
  obtain ⟨y2, hy2⟩ := hy2
  set y := max y1 y2
  have hb := hy1 y (le_max_left _ _)
  have ha := hy2 y (le_max_right _ _)
  rw [Real.dist_eq, sub_zero] at hb
  rw [Real.dist_eq] at ha
  set bnd := Real.exp (-∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ)) * (1 + 2 * ∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ))
  have hbnd : bnd < ε / 4 := lt_of_le_of_lt (le_abs_self _) hb
  -- averages along `N` for this `y`
  set A := ∑ pq ∈ pairsUpTo y, pairWeight pq
  set D := (#((range (Qy y)).filter (InE y)) : ℝ) / (Qy y)
  have hD : D ≤ bnd := density_inE_le y
  have hG := tendsto_avg_periodic (fy y) (Qy_pos y) (fy_periodic y)
  rw [avg_fy] at hG
  have hH := tendsto_avg_periodic (fun m => if InE y m then (1 : ℝ) else 0) (Qy_pos y)
    (fun m => by simp only [inE_periodic])
  have hHval : (∑ m ∈ range (Qy y), (if InE y m then (1 : ℝ) else 0)) / (Qy y) = D := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  rw [hHval] at hH
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hG) (ε / 4) (by positivity)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hH) (ε / 8) (by positivity)
  obtain ⟨N3, hN3⟩ := (Metric.tendsto_atTop.mp (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)))
    (ε / 8) (by positivity)
  refine ⟨max (max N1 N2) (max N3 1), fun N hN => ?_⟩
  have h1 := hN1 N (by omega)
  have h2 := hN2 N (by omega)
  have h3 := hN3 N (by omega)
  rw [Real.dist_eq] at h1 h2 h3 ⊢
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- the truncation error
  have htr : |(∑ m ∈ range N, rhoStar m) / N - (∑ m ∈ range N, fy y m) / N|
      ≤ (∑ m ∈ range N, (if InE y m then (1 : ℝ) else 0)) / N + 2 / N := by
    rw [← sub_div, abs_div, abs_of_pos hNpos, ← sum_sub_distrib]
    have hsmall : ∑ m ∈ range N, (if m < 2 then (1 : ℝ) else 0) ≤ 2 := by
      rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
      have : #((range N).filter (fun m => m < 2)) ≤ 2 := by
        calc #((range N).filter (fun m => m < 2)) ≤ #(range 2) := by
              apply card_le_card
              intro m hm
              simp only [mem_filter, mem_range] at hm ⊢
              exact hm.2
          _ = 2 := card_range 2
      exact_mod_cast this
    calc |∑ m ∈ range N, (rhoStar m - fy y m)| / N
        ≤ (∑ m ∈ range N, ((if InE y m then (1 : ℝ) else 0) + (if m < 2 then 1 else 0))) / N := by
          apply div_le_div_of_nonneg_right _ hNpos.le
          exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => abs_rhoStar_sub_fy y m)
      _ ≤ (∑ m ∈ range N, (if InE y m then (1 : ℝ) else 0)) / N + 2 / N := by
          rw [sum_add_distrib, add_div]
          exact add_le_add le_rfl (div_le_div_of_nonneg_right hsmall hNpos.le)
  have h2' : (∑ m ∈ range N, (if InE y m then (1 : ℝ) else 0)) / N < D + ε / 8 := by
    have := (abs_lt.mp h2).2
    linarith
  have h3' : 2 / (N : ℝ) < ε / 8 := by
    have := (abs_lt.mp h3).2
    linarith
  calc |(∑ m ∈ range N, rhoStar m) / N - meanRate|
      ≤ |(∑ m ∈ range N, rhoStar m) / N - (∑ m ∈ range N, fy y m) / N|
        + |(∑ m ∈ range N, fy y m) / N - A| + |A - meanRate| := by
        have := abs_sub_le ((∑ m ∈ range N, rhoStar m) / N) ((∑ m ∈ range N, fy y m) / N) A
        have := abs_sub_le ((∑ m ∈ range N, rhoStar m) / N) A meanRate
        linarith
    _ < ε := by linarith

end ArithmeticDynamics

/-! ════════════════════════ Part 15: Energy ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XV: the Kuramoto energy, its gradient structure, regularity of the vector field,
the Fréchet derivative at twisted states, and the quarter-twist energy formula (Theorem 5.6).
-/

namespace ArithmeticDynamics

open Finset Real

variable {n : ℕ} [NeZero n]

/-- The Kuramoto energy `E(θ) = -(K/(2φ(n))) ∑_i ∑_u cos(θ_{i+u} - θ_i)` on `X_n`. -/
noncomputable def energy (n : ℕ) [NeZero n] (K : ℝ) (θ : ZMod n → ℝ) : ℝ :=
  -(K / (2 * (Nat.totient n : ℝ))) * ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, cos (θ (i + u) - θ i)

/-- Reindexing identity behind the gradient structure. -/
theorem sum_sin_shift (x v : ZMod n → ℝ) :
    ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, sin (x (i + u) - x i) * v (i + u)
      = -∑ i : ZMod n, ∑ u : (ZMod n)ˣ, sin (x (i + u) - x i) * v i := by
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  have h1 : ∀ u : (ZMod n)ˣ, ∑ i : ZMod n, sin (x (i + u) - x i) * v (i + u)
      = -∑ j : ZMod n, sin (x (j + ((-u : (ZMod n)ˣ) : ZMod n)) - x j) * v j := by
    intro u
    rw [← Equiv.sum_comp (Equiv.subRight (u : ZMod n))]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [Equiv.subRight_apply, sub_add_cancel, Units.val_neg]
    rw [← sub_eq_add_neg, ← neg_sub (x (j - u)) (x j), sin_neg]
    ring
  rw [sum_congr rfl fun u _ => h1 u, sum_neg_distrib, neg_inj]
  exact Fintype.sum_equiv (Equiv.neg (ZMod n)ˣ)
    (fun u => ∑ j : ZMod n, sin (x (j + ((-u : (ZMod n)ˣ) : ZMod n)) - x j) * v j)
    (fun u => ∑ j : ZMod n, sin (x (j + (u : ZMod n)) - x j) * v j) (fun u => rfl)

/-- The Kuramoto vector field has zero sum, so `∑ θ_i` is conserved. -/
theorem sum_kuramotoField (K : ℝ) (x : ZMod n → ℝ) : ∑ i, kuramotoField n K x i = 0 := by
  unfold kuramotoField
  rw [← mul_sum]
  have h := sum_sin_shift x (fun _ => 1)
  simp only [mul_one] at h
  have : ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, sin (x (i + u) - x i) = 0 := by linarith
  rw [this, mul_zero]

/-- **Gradient structure.**  The Kuramoto field is `-∇E`: along every line,
`d/dt E(x + t v)|_{t=0} = -∑_i F(x)_i v_i`. -/
theorem energy_hasDerivAt_line (K : ℝ) (x v : ZMod n → ℝ) :
    HasDerivAt (fun t : ℝ => energy n K (x + t • v)) (-∑ i, kuramotoField n K x i * v i) 0 := by
  unfold energy
  have hterm : ∀ (i : ZMod n) (u : (ZMod n)ˣ),
      HasDerivAt (fun t : ℝ => cos ((x + t • v) (i + u) - (x + t • v) i))
        (-sin (x (i + u) - x i) * (v (i + u) - v i)) 0 := by
    intro i u
    have hl : HasDerivAt (fun t : ℝ => (x + t • v) (i + u) - (x + t • v) i)
        (v (i + u) - v i) 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have ha := ((hasDerivAt_id (0 : ℝ)).mul_const (v (i + u))).const_add (x (i + u))
      have hb := ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (x i)
      have := ha.fun_sub hb
      simpa using this
    have := hl.cos
    simpa [mul_comm] using this
  have hsum := HasDerivAt.fun_sum (u := univ) fun i _ =>
    HasDerivAt.fun_sum (u := univ) fun u _ => hterm i u
  convert hsum.const_mul (-(K / (2 * (Nat.totient n : ℝ)))) using 1
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  have hs := sum_sin_shift x v
  have e1 : ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, -sin (x (i + u) - x i) * (v (i + u) - v i)
      = -(∑ i : ZMod n, ∑ u : (ZMod n)ˣ, sin (x (i + u) - x i) * v (i + u))
        + ∑ i : ZMod n, ∑ u : (ZMod n)ˣ, sin (x (i + u) - x i) * v i := by
    rw [← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    ring
  rw [e1, hs]
  unfold kuramotoField
  simp_rw [mul_assoc, ← mul_sum, sum_mul]
  field_simp
  ring

/-! ### Regularity of the vector field -/

theorem contDiff_kuramotoField (K : ℝ) : ContDiff ℝ 1 (kuramotoField n K) := by
  unfold kuramotoField
  fun_prop

theorem lipschitz_kuramotoField (K : ℝ) : ∃ L, LipschitzWith L (kuramotoField n K) := by
  refine ⟨⟨2 * |K|, by positivity⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hd : 0 ≤ dist x y := dist_nonneg
  show dist (kuramotoField n K x) (kuramotoField n K y) ≤ 2 * |K| * dist x y
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  rw [Real.dist_eq]
  unfold kuramotoField
  rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_div, abs_of_pos hφ]
  have hb : ∀ u : (ZMod n)ˣ, |sin (x (i + u) - x i) - sin (y (i + u) - y i)| ≤ 2 * dist x y := by
    intro u
    refine (abs_sin_sub_sin_le _ _).trans ?_
    have h1 : |x (i + u) - y (i + u)| ≤ dist x y := by
      rw [← Real.dist_eq]; exact dist_le_pi_dist x y _
    have h2 : |x i - y i| ≤ dist x y := by
      rw [← Real.dist_eq]; exact dist_le_pi_dist x y _
    calc |x (i + u) - x i - (y (i + u) - y i)| = |(x (i + u) - y (i + u)) - (x i - y i)| := by
          ring_nf
      _ ≤ |x (i + u) - y (i + u)| + |x i - y i| := abs_sub _ _
      _ ≤ 2 * dist x y := by linarith
  calc |K| / (Nat.totient n : ℝ) * |∑ u : (ZMod n)ˣ, (sin (x (i + u) - x i) - sin (y (i + u) - y i))|
      ≤ |K| / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, 2 * dist x y := by
        gcongr
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u _ => hb u)
    _ = 2 * |K| * dist x y := by
        rw [sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
        field_simp

theorem analyticAt_energy (K : ℝ) (x : ZMod n → ℝ) : AnalyticAt ℝ (energy n K) x := by
  unfold energy
  have hL : ∀ (i : ZMod n) (u : (ZMod n)ˣ),
      AnalyticAt ℝ (fun θ : ZMod n → ℝ => cos (θ (i + u) - θ i)) x := by
    intro i u
    have hlin : AnalyticAt ℝ (fun θ : ZMod n → ℝ => θ (i + u) - θ i) x :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ZMod n => ℝ) (i + u))
        - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ZMod n => ℝ) i).analyticAt x
    exact analyticAt_cos.comp hlin
  refine analyticAt_const.mul ?_
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact Finset.analyticAt_fun_sum _ fun u _ => hL i u

/-! ### The Fréchet derivative at a point, and at twisted states -/

/-- The real Jacobian `(J f)_i = (K/φ) ∑_u w_u (f_{i+u} - f_i)` at the `m`-twisted state. -/
noncomputable def jacR (K : ℝ) (m : ZMod n) (f : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  K / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, twistWeight n m u * (f (i + u) - f i)

theorem fderiv_kuramotoField (K : ℝ) (θ f : ZMod n → ℝ) (i : ZMod n) :
    fderiv ℝ (kuramotoField n K) θ f i
      = K / (Nat.totient n : ℝ) * ∑ u : (ZMod n)ˣ, cos (θ (i + u) - θ i) * (f (i + u) - f i) := by
  have hdiff : DifferentiableAt ℝ (kuramotoField n K) θ :=
    (contDiff_kuramotoField K).differentiable one_ne_zero θ
  have hline : HasDerivAt (fun t : ℝ => θ + t • f) f 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const f).const_add θ
    simpa using this
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hi := (hasDerivAt_pi.mp hcomp) i
  have hk := hasDerivAt_kuramotoField n K θ f i
  have heq : (fun t : ℝ => (kuramotoField n K ∘ fun t => θ + t • f) t i)
      = fun t : ℝ => kuramotoField n K (fun x => θ x + t * f x) i := by
    funext t
    simp only [Function.comp_apply]
    congr 1
  rw [heq] at hi
  exact hi.unique hk

theorem fderiv_kuramotoField_twisted (K : ℝ) (a : ℕ) (f : ZMod n → ℝ) (i : ZMod n) :
    fderiv ℝ (kuramotoField n K) (twisted n a) f i = jacR K (a : ZMod n) f i := by
  rw [fderiv_kuramotoField]
  unfold jacR
  simp only [cos_twisted_diff]

theorem jac_re (K : ℝ) (m : ZMod n) (f : ZMod n → ℂ) (i : ZMod n) :
    (jac n K m f i).re = jacR K m (fun j => (f j).re) i := by
  unfold jac jacR
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine sum_congr rfl fun u _ => ?_
  rw [Complex.re_ofReal_mul, Complex.sub_re]

/-! ### The energy at quarter twists (Theorem 5.6 (i), (ii)) -/

/-- The two-site perturbation `δ = t (e₀ - e₁)`. -/
noncomputable def kick (n : ℕ) (t : ℝ) : ZMod n → ℝ :=
  fun j => t * ((if j = 0 then 1 else 0) - (if j = 1 then 1 else 0))

theorem sum_kick (t : ℝ) : ∑ j, kick n t j = 0 := by
  unfold kick
  rw [← mul_sum, sum_sub_distrib, sum_ite_eq', sum_ite_eq']
  simp

omit [NeZero n] in
theorem sin_kick (h01 : (0 : ZMod n) ≠ 1) (t : ℝ) (j : ZMod n) :
    sin (kick n t j) = sin t * ((if j = 0 then 1 else 0) - (if j = 1 then 1 else 0)) := by
  unfold kick
  by_cases h0 : j = 0
  · subst h0; simp [h01]
  · by_cases h1 : j = 1
    · subst h1; simp [h01.symm, sin_neg]
    · simp [h0, h1]

omit [NeZero n] in
theorem cos_kick (h01 : (0 : ZMod n) ≠ 1) (t : ℝ) (j : ZMod n) :
    cos (kick n t j) = 1 + (cos t - 1) * ((if j = 0 then 1 else 0) + (if j = 1 then 1 else 0)) := by
  unfold kick
  by_cases h0 : j = 0
  · subst h0; simp [h01]
  · by_cases h1 : j = 1
    · subst h1; simp [h01.symm, cos_neg]
    · simp [h0, h1]

theorem sum_ind_mul (g : ZMod n → ℝ) (c : ZMod n) :
    ∑ i : ZMod n, (if i = c then (1 : ℝ) else 0) * g i = g c := by
  simp [ite_mul]

/-- The edge sum of the perturbation along a fixed generator `x`. -/
theorem sum_sin_kick (h01 : (0 : ZMod n) ≠ 1) (t : ℝ) (x : ZMod n) :
    ∑ i : ZMod n, sin (kick n t (i + x) - kick n t i)
      = 2 * sin t * (cos t - 1) * ((if x = -1 then 1 else 0) - (if x = 1 then 1 else 0)) := by
  set d : ZMod n → ℝ := fun j => (if j = 0 then 1 else 0) - (if j = 1 then 1 else 0) with hd
  set e : ZMod n → ℝ := fun j => (if j = 0 then 1 else 0) + (if j = 1 then 1 else 0) with he
  have hs : ∀ j, sin (kick n t j) = sin t * d j := fun j => sin_kick h01 t j
  have hc : ∀ j, cos (kick n t j) = 1 + (cos t - 1) * e j := fun j => cos_kick h01 t j
  have hsum_d : ∑ j : ZMod n, d j = 0 := by
    simp only [hd, sum_sub_distrib, sum_ite_eq', mem_univ, if_true, sub_self]
  have hsum_dx : ∑ i : ZMod n, d (i + x) = 0 := by
    have := Equiv.sum_comp (Equiv.addRight x) d
    simp only [Equiv.coe_addRight] at this
    rw [this]
    exact hsum_d
  have hde : ∑ i : ZMod n, d (i + x) * e i = d x + d (1 + x) := by
    simp only [he, mul_add, sum_add_distrib]
    simp only [mul_comm (d _), sum_ind_mul (fun i => d (i + x))]
    simp
  have hed : ∑ i : ZMod n, e (i + x) * d i = e x - e (1 + x) := by
    simp only [hd, mul_sub, sum_sub_distrib]
    simp only [mul_comm (e _), sum_ind_mul (fun i => e (i + x))]
    simp
  have expand : ∀ i, sin (kick n t (i + x) - kick n t i)
      = sin t * d (i + x) + sin t * (cos t - 1) * (d (i + x) * e i)
        - sin t * d i - sin t * (cos t - 1) * (e (i + x) * d i) := by
    intro i
    rw [sin_sub, hs, hs, hc, hc]
    ring
  rw [sum_congr rfl fun i _ => expand i, sum_sub_distrib, sum_sub_distrib, sum_add_distrib,
    ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum, hsum_dx, hde, hsum_d, hed]
  have e1 : (1 + x = 0) ↔ x = -1 := by
    constructor
    · intro h; linear_combination h
    · intro h; rw [h]; ring
  have e2 : (1 + x = 1) ↔ x = 0 := by
    constructor
    · intro h; linear_combination h
    · intro h; rw [h]; ring
  simp only [hd, he, e1, e2]
  by_cases h0 : x = 0
  · subst h0
    have : (0 : ZMod n) ≠ -1 := by
      intro h; apply h01; linear_combination -h
    simp [h01, this]
  · by_cases h1 : x = 1
    · subst h1
      simp [h01.symm]
      split_ifs <;> ring
    · simp [h0, h1]
      split_ifs <;> ring

/-- The sine of the phase lag along generator `u` at the `a`-twisted state. -/
noncomputable def sigma (n : ℕ) [NeZero n] (a : ℕ) (u : ZMod n) : ℝ :=
  (ZMod.stdAddChar ((a : ZMod n) * u) : ℂ).im

theorem sigma_neg (a : ℕ) (u : ZMod n) : sigma n a (-u) = -sigma n a u := by
  unfold sigma
  rw [mul_neg, ← conj_stdAddChar, Complex.conj_im]

/-- **Theorem 5.6 (i).**  If every edge weight vanishes, the energy of the twisted state is `0`. -/
theorem energy_twisted_eq_zero (K : ℝ) (a : ℕ) (hz : ∀ u, twistWeight n (a : ZMod n) u = 0) :
    energy n K (twisted n a) = 0 := by
  unfold energy
  simp [cos_twisted_diff, hz]

/-- **Theorem 5.6 (ii), general form.**  If every edge weight at the `a`-twisted state vanishes,
then `E(θ + t(e₀ - e₁)) = (2K/φ(n)) σ sin t (1 - cos t)` with `σ = sin(2πa/n)`. -/
theorem energy_twisted_kick (K : ℝ) (a : ℕ) (hz : ∀ u, twistWeight n (a : ZMod n) u = 0)
    (h01 : (0 : ZMod n) ≠ 1) (t : ℝ) :
    energy n K (twisted n a + kick n t)
      = 2 * K / (Nat.totient n : ℝ) * sigma n a 1 * sin t * (1 - cos t) := by
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  have hterm : ∀ (i : ZMod n) (u : (ZMod n)ˣ),
      cos ((twisted n a + kick n t) (i + u) - (twisted n a + kick n t) i)
        = -(sigma n a u * sin (kick n t (i + u) - kick n t i)) := by
    intro i u
    have e : (twisted n a + kick n t) (i + u) - (twisted n a + kick n t) i
        = (twisted n a (i + u) - twisted n a i) + (kick n t (i + u) - kick n t i) := by
      simp only [Pi.add_apply]; ring
    rw [e, cos_add, cos_twisted_diff, hz, sin_twisted_diff]
    unfold sigma
    ring
  have hu : ∀ u : (ZMod n)ˣ, ((u : ZMod n) = -1 ↔ u = -1) := fun u => by
    rw [Units.ext_iff, Units.val_neg, Units.val_one]
  have hu1 : ∀ u : (ZMod n)ˣ, ((u : ZMod n) = 1 ↔ u = 1) := fun u => by
    rw [Units.ext_iff, Units.val_one]
  set C := 2 * sin t * (cos t - 1) with hC
  have hsum : ∑ i : ZMod n, ∑ u : (ZMod n)ˣ,
      cos ((twisted n a + kick n t) (i + u) - (twisted n a + kick n t) i)
        = -(C * (sigma n a (-1) - sigma n a 1)) := by
    rw [sum_congr rfl fun i _ => sum_congr rfl fun u _ => hterm i u]
    simp only [sum_neg_distrib]
    rw [sum_comm]
    congr 1
    have h1 : ∀ u : (ZMod n)ˣ, ∑ i : ZMod n, sigma n a u * sin (kick n t (i + u) - kick n t i)
        = C * ((if u = -1 then sigma n a (-1) else 0) - (if u = 1 then sigma n a 1 else 0)) := by
      intro u
      rw [← mul_sum, sum_sin_kick h01]
      simp only [hu, hu1]
      rcases em (u = -1) with ha | ha <;> rcases em (u = 1) with hb | hb
      · have e1 : (u : ZMod n) = -1 := (hu u).mpr ha
        have e2 : (u : ZMod n) = 1 := (hu1 u).mpr hb
        have e3 : sigma n a (-1) = sigma n a 1 := by rw [← e1, e2]
        rw [if_pos ha, if_pos hb, if_pos ha, if_pos hb, e3]
        ring
      · have e1 : (u : ZMod n) = -1 := (hu u).mpr ha
        rw [if_pos ha, if_neg hb, if_pos ha, if_neg hb, e1]
        ring
      · have e2 : (u : ZMod n) = 1 := (hu1 u).mpr hb
        rw [if_neg ha, if_pos hb, if_neg ha, if_pos hb, e2]
        ring
      · rw [if_neg ha, if_neg hb, if_neg ha, if_neg hb]
        ring
    rw [sum_congr rfl fun u _ => h1 u, ← mul_sum, sum_sub_distrib, sum_ite_eq', sum_ite_eq']
    simp
  unfold energy
  rw [hsum, sigma_neg, hC]
  field_simp
  ring

omit [NeZero n] in
theorem natCast_quarter (h4 : 4 ∣ n) :
    (((3 * (n / 4) : ℕ)) : ZMod n) = -((n / 4 : ℕ) : ZMod n) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← Nat.cast_add]
  have e : 3 * (n / 4) + n / 4 = n := by
    have := Nat.div_mul_cancel h4
    omega
  rw [e, ZMod.natCast_self]

theorem sigma_quarter (h4 : 4 ∣ n) : sigma n (n / 4) 1 = 1 := by
  unfold sigma
  rw [mul_one, stdAddChar_natCast_im]
  obtain ⟨c, hc⟩ := h4
  have hc0 : (c : ℝ) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; exact NeZero.ne n (by simpa using hc)
    exact_mod_cast this
  have hdiv : n / 4 = c := by rw [hc]; exact Nat.mul_div_cancel_left c (by norm_num)
  rw [hdiv, hc]
  push_cast
  have : 2 * π * c / (4 * c) = π / 2 := by field_simp; ring
  rw [this, sin_pi_div_two]

theorem sigma_three_quarter (h4 : 4 ∣ n) : sigma n (3 * (n / 4)) 1 = -1 := by
  have h : sigma n (3 * (n / 4)) 1 = sigma n (n / 4) (-1) := by
    unfold sigma
    rw [natCast_quarter h4, neg_mul, mul_neg]
  rw [h, sigma_neg, sigma_quarter h4]

theorem twistWeight_three_quarter (h4 : 4 ∣ n) (u : (ZMod n)ˣ) :
    twistWeight n ((3 * (n / 4) : ℕ) : ZMod n) u = 0 := by
  rw [natCast_quarter h4, twistWeight_neg, twistWeight_quarter h4]

theorem zero_ne_one_of_four_dvd (h4 : 4 ∣ n) : (0 : ZMod n) ≠ 1 := by
  have : 1 < n := by
    obtain ⟨c, hc⟩ := h4
    have := NeZero.ne n
    omega
  haveI : Fact (1 < n) := ⟨this⟩
  exact zero_ne_one

/-- **Theorem 5.6 (ii) for `m = n/4`.** -/
theorem energy_quarter_kick (h4 : 4 ∣ n) (K t : ℝ) :
    energy n K (twisted n (n / 4) + kick n t)
      = 2 * K / (Nat.totient n : ℝ) * sin t * (1 - cos t) := by
  rw [energy_twisted_kick K _ (fun u => twistWeight_quarter h4 u) (zero_ne_one_of_four_dvd h4),
    sigma_quarter h4]
  ring

/-- **Theorem 5.6 (ii) for `m = 3n/4`.** -/
theorem energy_three_quarter_kick (h4 : 4 ∣ n) (K t : ℝ) :
    energy n K (twisted n (3 * (n / 4)) + kick n t)
      = -(2 * K / (Nat.totient n : ℝ) * sin t * (1 - cos t)) := by
  rw [energy_twisted_kick K _ (fun u => twistWeight_three_quarter h4 u)
    (zero_ne_one_of_four_dvd h4), sigma_three_quarter h4]
  ring

end ArithmeticDynamics

/-! ════════════════════════ Part 16: Nonlinear ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XVI: nonlinear stability conclusions (Theorems 5.4, 5.5, 5.6 (iii), Corollary 5.7).

Three classical theorems of dynamical systems are used as explicit hypotheses.  Each is stated
for *every* vector field on `ℝ^{ℤ/n}` satisfying the standard assumptions, so each is a genuine
classical theorem and not a statement tailored to the Kuramoto model:
* `LyapunovIndirectStability`  — Lyapunov's indirect method (stability), on an invariant level set;
* `LyapunovIndirectInstability` — Lyapunov's instability theorem by first approximation;
* `AbsilKurdyka` — Absil–Kurdyka (2006): for an analytic energy, a stable equilibrium of the
  gradient flow is a local minimum.
-/

namespace ArithmeticDynamics

open Finset Real Filter Topology

variable {n : ℕ} [NeZero n]

/-! ### Dynamical notions (Euclidean norm `sqNorm`) -/

/-- `x` is a solution of `ẋ = F(x)` defined for all times. -/
def IsSolution (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (x : ℝ → ZMod n → ℝ) : Prop :=
  ∀ t, HasDerivAt x (F (x t)) t

/-- Lyapunov stability of an equilibrium `xs`. -/
def LyapunovStable (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs : ZMod n → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, IsSolution F x → sqNorm (x 0 - xs) < δ →
    ∀ t ≥ 0, sqNorm (x t - xs) < ε

/-- Local exponential stability with rate `ρ` on the level set `∑ x = ∑ xs`
("modulo rotation" for the Kuramoto model). -/
def ExpStableOnLevel (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs : ZMod n → ℝ) (ρ : ℝ) : Prop :=
  ∃ δ > 0, ∀ x, IsSolution F x → ∑ j, x 0 j = ∑ j, xs j → sqNorm (x 0 - xs) < δ →
    ∀ t ≥ 0, sqNorm (x t - xs) ≤ Real.exp (-2 * ρ * t) * sqNorm (x 0 - xs)

/-! ### The classical theorems, as hypotheses -/

variable (n) in
/-- **Lyapunov's indirect method (stability).**  For a `C¹`, globally Lipschitz field with zero
sum and an equilibrium whose linearisation is `≤ -r` on sum-zero vectors, the equilibrium is
exponentially stable with every rate `r' < r` on its level set. -/
def LyapunovIndirectStability : Prop :=
  ∀ (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs : ZMod n → ℝ) (r : ℝ),
    ContDiff ℝ 1 F → (∃ L, LipschitzWith L F) → F xs = 0 → (∀ x, ∑ j, F x j = 0) → 0 < r →
    (∀ w : ZMod n → ℝ, ∑ j, w j = 0 → ∑ j, fderiv ℝ F xs w j * w j ≤ -r * sqNorm w) →
    ∀ r', 0 < r' → r' < r → ExpStableOnLevel F xs r'

variable (n) in
/-- **Lyapunov's instability theorem by first approximation.**  A real eigenvalue `μ > 0` of the
linearisation at an equilibrium of a `C¹`, globally Lipschitz field makes it unstable. -/
def LyapunovIndirectInstability : Prop :=
  ∀ (F : (ZMod n → ℝ) → (ZMod n → ℝ)) (xs v : ZMod n → ℝ) (μ : ℝ),
    ContDiff ℝ 1 F → (∃ L, LipschitzWith L F) → F xs = 0 → v ≠ 0 →
    fderiv ℝ F xs v = μ • v → 0 < μ → ¬ LyapunovStable F xs

variable (n) in
/-- **Absil–Kurdyka.**  If `E` is real analytic and `F = -∇E` is `C¹` and globally Lipschitz,
then every Lyapunov-stable equilibrium of `ẋ = F(x)` is a local minimum of `E`. -/
def AbsilKurdyka : Prop :=
  ∀ (E : (ZMod n → ℝ) → ℝ) (F : (ZMod n → ℝ) → (ZMod n → ℝ)),
    (∀ x, AnalyticAt ℝ E x) →
    (∀ x v, HasDerivAt (fun t : ℝ => E (x + t • v)) (-∑ j, F x j * v j) 0) →
    ContDiff ℝ 1 F → (∃ L, LipschitzWith L F) →
    ∀ xs, F xs = 0 → LyapunovStable F xs → IsLocalMin E xs

/-! ### Jacobians at the hexagonal and synchronous states -/

theorem kuramotoField_twisted_eq (K : ℝ) (a : ℕ) : kuramotoField n K (twisted n a) = 0 :=
  funext fun i => kuramotoField_twisted n K a i

theorem jacR_hex (h6 : 6 ∣ n) (K : ℝ) (f : ZMod n → ℝ) (i : ZMod n) :
    jacR K ((n / 6 : ℕ) : ZMod n) f i = -(K / (2 * (Nat.totient n : ℝ))) * lapR f i := by
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  unfold jacR lapR
  simp only [twistWeight_hex h6]
  rw [← mul_sum, sum_sub_distrib, sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
  field_simp
  ring

theorem twistWeight_zero (u : (ZMod n)ˣ) : twistWeight n 0 u = 1 := by
  unfold twistWeight
  simp

theorem jacR_sync (K : ℝ) (f : ZMod n → ℝ) (i : ZMod n) :
    jacR K 0 f i = -(K / (Nat.totient n : ℝ)) * lapR f i := by
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  unfold jacR lapR
  simp only [twistWeight_zero, one_mul]
  rw [sum_sub_distrib, sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
  ring

theorem lapEig_ge_half (k : ZMod n) (hk : k ≠ 0) : (Nat.totient n : ℝ) / 2 ≤ lapEig n k := by
  have h := r_le_half_of_one_lt (one_lt_addOrderOf hk)
  have hφ : (0 : ℝ) ≤ (Nat.totient n : ℝ) := Nat.cast_nonneg _
  unfold lapEig
  nlinarith

theorem quad_upper_aux : ∀ k : ZMod n, k ≠ 0 → lapEig n k ≤ ∑ k', |lapEig n k'| := fun k _ =>
  (le_abs_self _).trans (single_le_sum (f := fun k' => |lapEig n k'|)
    (fun _ _ => abs_nonneg _) (mem_univ k))

/-- The linearisation at the hexagonal state is `≤ -K/4` on sum-zero vectors. -/
theorem quad_hex (h6 : 6 ∣ n) {K : ℝ} (hK : 0 ≤ K) (w : ZMod n → ℝ) (hw : ∑ j, w j = 0) :
    ∑ j, jacR K ((n / 6 : ℕ) : ZMod n) w j * w j ≤ -(K / 4) * sqNorm w := by
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hq := (quadForm_bounds w hw lapEig_ge_half quad_upper_aux).1
  simp_rw [jacR_hex h6, mul_assoc, ← mul_sum]
  have hc : 0 ≤ K / (2 * (Nat.totient n : ℝ)) := by positivity
  have := mul_le_mul_of_nonneg_left hq hc
  have e : K / (2 * (Nat.totient n : ℝ)) * ((Nat.totient n : ℝ) / 2 * sqNorm w)
      = K / 4 * sqNorm w := by field_simp; ring
  linarith

/-- The linearisation at the synchronous state is `≤ -K/2` on sum-zero vectors. -/
theorem quad_sync {K : ℝ} (hK : 0 ≤ K) (w : ZMod n → ℝ) (hw : ∑ j, w j = 0) :
    ∑ j, jacR K 0 w j * w j ≤ -(K / 2) * sqNorm w := by
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hq := (quadForm_bounds w hw lapEig_ge_half quad_upper_aux).1
  simp_rw [jacR_sync, mul_assoc, ← mul_sum]
  have hc : 0 ≤ K / (Nat.totient n : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hq hc
  have e : K / (Nat.totient n : ℝ) * ((Nat.totient n : ℝ) / 2 * sqNorm w) = K / 2 * sqNorm w := by
    field_simp
  linarith

/-! ### Theorem 5.5: exponential stability of the hexagonal and synchronous states -/

/-- **Theorem 5.5.**  For `6 ∣ n` the hexagonal state is exponentially stable modulo rotation
with every rate `r' < K/4`. -/
theorem hex_expStable (hL : LyapunovIndirectStability n) (h6 : 6 ∣ n) {K : ℝ} (hK : 0 < K)
    {r' : ℝ} (hr' : 0 < r') (hr : r' < K / 4) :
    ExpStableOnLevel (kuramotoField n K) (twisted n (n / 6)) r' :=
  hL _ _ (K / 4) (contDiff_kuramotoField K) (lipschitz_kuramotoField K)
    (kuramotoField_twisted_eq K _) (sum_kuramotoField K) (by positivity)
    (fun w hw => by
      simp_rw [fderiv_kuramotoField_twisted]
      exact quad_hex h6 hK.le w hw) r' hr' hr

/-- **Theorem 5.5 (synchronous state).**  The synchronous state is exponentially stable modulo
rotation with every rate `r' < K/2`. -/
theorem sync_expStable (hL : LyapunovIndirectStability n) {K : ℝ} (hK : 0 < K)
    {r' : ℝ} (hr' : 0 < r') (hr : r' < K / 2) :
    ExpStableOnLevel (kuramotoField n K) (twisted n 0) r' :=
  hL _ _ (K / 2) (contDiff_kuramotoField K) (lipschitz_kuramotoField K)
    (kuramotoField_twisted_eq K _) (sum_kuramotoField K) (by positivity)
    (fun w hw => by
      simp_rw [fderiv_kuramotoField_twisted]
      have : ((0 : ℕ) : ZMod n) = 0 := Nat.cast_zero
      rw [this]
      exact quad_sync hK.le w hw) r' hr' hr

/-! ### Theorem 5.5: the linear rates are exact -/

omit [NeZero n] in
theorem twoSmallest_two_three (h6 : 6 ∣ n) : TwoSmallest n 2 3 := by
  refine ⟨Nat.prime_two, Nat.prime_three, dvd_trans (by norm_num) h6, dvd_trans (by norm_num) h6,
    by norm_num, fun ℓ hℓ _ => hℓ.two_le, fun ℓ hℓ _ hne => ?_⟩
  have := hℓ.two_le
  omega

/-- **Theorem 5.5, spectrum.**  The eigenvalues `-(K/2)(1 - r(ord k))`, `k ≠ 0`, of the hexagonal
Jacobian lie in `[-K, -K/4]`, and `-K/4` is attained exactly at the residues of order `6`. -/
theorem hex_spectrum (h6 : 6 ∣ n) {K : ℝ} (hK : 0 < K) (k : ZMod n) (hk : k ≠ 0) :
    -K ≤ -(K / 2) * (1 - r (addOrderOf k)) ∧ -(K / 2) * (1 - r (addOrderOf k)) ≤ -(K / 4) ∧
      (-(K / 2) * (1 - r (addOrderOf k)) = -(K / 4) ↔ addOrderOf k = 6) := by
  have hM := one_lt_addOrderOf hk
  have hlo : -1 ≤ r (addOrderOf k) := by
    have h1 := abs_r_le (addOrderOf k)
    have h2 : (1 : ℝ) ≤ (Nat.totient (addOrderOf k) : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    have h3 : 1 / (Nat.totient (addOrderOf k) : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact h2
    linarith [neg_abs_le (r (addOrderOf k))]
  have hhi := r_le_half_of_one_lt hM
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have key := r_eq_max_iff (twoSmallest_two_three h6) hM (addOrderOf_dvd_self k)
  norm_num at key
  constructor
  · intro h
    have : r (addOrderOf k) = 1 / 2 := by
      have hK2 : K / 2 ≠ 0 := by positivity
      field_simp at h
      linarith
    exact key.mp this
  · intro h
    rw [key.mpr h]
    ring

/-- **Theorem 5.5, synchronous state.**  At `m = 0` the Jacobian is `-(K/φ) L`, with eigenvalues
`-K(1 - r(ord k)) ≤ -K/2` for `k ≠ 0`; for `6 ∣ n` the value `-K/2` is attained. -/
theorem jac_sync_chi (K : ℝ) (k i : ZMod n) :
    jac n K 0 (chi n k) i = ((-K * (1 - r (addOrderOf k)) : ℝ) : ℂ) * chi n k i := by
  rw [jac_chi, zero_add, zero_sub, addOrderOf_neg, addOrderOf_zero, r_one]
  congr 2
  ring

theorem sync_rate (K : ℝ) (hK : 0 ≤ K) (k : ZMod n) (hk : k ≠ 0) :
    -K * (1 - r (addOrderOf k)) ≤ -(K / 2) := by
  have := r_le_half_of_one_lt (one_lt_addOrderOf hk)
  nlinarith

theorem sync_rate_attained (h6 : 6 ∣ n) (K : ℝ) :
    -K * (1 - r (addOrderOf ((n / 6 : ℕ) : ZMod n))) = -(K / 2) := by
  rw [addOrderOf_natCast_div h6, r_six]
  ring

/-! ### Theorem 5.4 (c): nonlinear instability -/

theorem chi_zero (k : ZMod n) : chi n k 0 = 1 := by
  unfold chi
  simp

/-- **Theorem 5.4 (c), nonlinear form.**  If `m ≠ 0` has order `∉ {4, 6}`, the `m`-twisted state
is (Lyapunov) unstable. -/
theorem twisted_unstable_nonlinear (hI : LyapunovIndirectInstability n) {K : ℝ} (hK : 0 < K)
    {a : ℕ} (hm : (a : ZMod n) ≠ 0) (h4 : addOrderOf (a : ZMod n) ≠ 4)
    (h6 : addOrderOf (a : ZMod n) ≠ 6) :
    ¬ LyapunovStable (kuramotoField n K) (twisted n a) := by
  set m : ZMod n := (a : ZMod n)
  set v : ZMod n → ℝ := fun j => (chi n m j).re with hv
  set μ := K * g (addOrderOf m)
  have hμ : 0 < μ := (twisted_unstable hK hm h4 h6).2
  refine hI _ _ v μ (contDiff_kuramotoField K) (lipschitz_kuramotoField K)
    (kuramotoField_twisted_eq K a) ?_ ?_ hμ
  · intro h
    have := congrFun h 0
    simp [hv, chi_zero] at this
  · funext i
    rw [Pi.smul_apply, smul_eq_mul, fderiv_kuramotoField_twisted]
    have h := congrArg Complex.re (jac_chi_self K m i)
    rw [jac_re, Complex.re_ofReal_mul] at h
    exact h

/-! ### Theorem 5.6 (iii): quarter twists are not minima, hence unstable -/

theorem norm_kick_le (τ : ℝ) (hτ : 0 ≤ τ) : ‖kick n (-τ)‖ ≤ τ := by
  refine (pi_norm_le_iff_of_nonneg hτ).mpr fun j => ?_
  unfold kick
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hτ]
  have : |(if j = 0 then (1 : ℝ) else 0) - (if j = 1 then 1 else 0)| ≤ 1 := by
    split_ifs <;> norm_num
  nlinarith

theorem norm_kick_le' (τ : ℝ) (hτ : 0 ≤ τ) : ‖kick n τ‖ ≤ τ := by
  have := norm_kick_le (n := n) τ hτ
  have e : kick n τ = -kick n (-τ) := by
    funext j; unfold kick; simp only [Pi.neg_apply]; ring
  rwa [e, norm_neg]

theorem sin_mul_one_sub_cos_pos {τ : ℝ} (h0 : 0 < τ) (h1 : τ ≤ 1) :
    0 < sin τ * (1 - cos τ) := by
  have hπ : τ < π := lt_of_le_of_lt h1 (by linarith [pi_gt_three])
  have hs := sin_pos_of_pos_of_lt_pi h0 hπ
  have hc : cos τ < 1 := by
    have := cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h0
    rwa [cos_zero] at this
  exact mul_pos hs (by linarith)

/-- A local minimum would be beaten by a small two-site kick of energy `< 0 = E(θ)`. -/
theorem not_isLocalMin_of_kick {K : ℝ} (hK : 0 < K) (θ : ZMod n → ℝ) (hE0 : energy n K θ = 0)
    (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hform : ∀ t, energy n K (θ + kick n t)
      = s * (2 * K / (Nat.totient n : ℝ) * sin t * (1 - cos t))) :
    ¬ IsLocalMin (energy n K) θ := by
  intro hmin
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hmin
  set τ := min (ε / 2) 1 with hτ
  have hτ0 : 0 < τ := lt_min (by positivity) one_pos
  have hτ1 : τ ≤ 1 := min_le_right _ _
  have hτε : τ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hpos := sin_mul_one_sub_cos_pos hτ0 hτ1
  have hc : 0 < 2 * K / (Nat.totient n : ℝ) := by positivity
  set t := -s * τ with ht
  have hdist : dist (θ + kick n t) θ < ε := by
    rw [dist_eq_norm, add_sub_cancel_left]
    rcases hs with rfl | rfl
    · have : t = -τ := by rw [ht]; ring
      rw [this]
      exact lt_of_le_of_lt (norm_kick_le τ hτ0.le) hτε
    · have : t = τ := by rw [ht]; ring
      rw [this]
      exact lt_of_le_of_lt (norm_kick_le' τ hτ0.le) hτε
  have hle := hball hdist
  rw [hE0, hform t] at hle
  have hval : s * (2 * K / (Nat.totient n : ℝ) * sin t * (1 - cos t))
      = -(2 * K / (Nat.totient n : ℝ) * (sin τ * (1 - cos τ))) := by
    rcases hs with rfl | rfl
    · have : t = -τ := by rw [ht]; ring
      rw [this, sin_neg, cos_neg]; ring
    · have : t = τ := by rw [ht]; ring
      rw [this]; ring
  rw [hval] at hle
  have := mul_pos hc hpos
  linarith

/-- **Theorem 5.6 (iii).**  The quarter twist `m = n/4` is not a local minimum of the energy. -/
theorem quarter_not_isLocalMin (h4 : 4 ∣ n) {K : ℝ} (hK : 0 < K) :
    ¬ IsLocalMin (energy n K) (twisted n (n / 4)) :=
  not_isLocalMin_of_kick hK _
    (energy_twisted_eq_zero K _ fun u => twistWeight_quarter h4 u) 1 (Or.inl rfl)
    (fun t => by rw [energy_quarter_kick h4, one_mul])

/-- **Theorem 5.6 (iii).**  The quarter twist `m = 3n/4` is not a local minimum of the energy. -/
theorem three_quarter_not_isLocalMin (h4 : 4 ∣ n) {K : ℝ} (hK : 0 < K) :
    ¬ IsLocalMin (energy n K) (twisted n (3 * (n / 4))) :=
  not_isLocalMin_of_kick hK _
    (energy_twisted_eq_zero K _ fun u => twistWeight_three_quarter h4 u) (-1) (Or.inr rfl)
    (fun t => by rw [energy_three_quarter_kick h4]; ring)

/-- **Theorem 5.6 (iii).**  Under Absil–Kurdyka, the quarter twists are unstable. -/
theorem quarter_unstable (hAK : AbsilKurdyka n) (h4 : 4 ∣ n) {K : ℝ} (hK : 0 < K) :
    ¬ LyapunovStable (kuramotoField n K) (twisted n (n / 4)) ∧
      ¬ LyapunovStable (kuramotoField n K) (twisted n (3 * (n / 4))) := by
  constructor
  · intro hst
    exact quarter_not_isLocalMin h4 hK
      (hAK (energy n K) (kuramotoField n K) (analyticAt_energy K) (energy_hasDerivAt_line K)
        (contDiff_kuramotoField K) (lipschitz_kuramotoField K) _
        (kuramotoField_twisted_eq K _) hst)
  · intro hst
    exact three_quarter_not_isLocalMin h4 hK
      (hAK (energy n K) (kuramotoField n K) (analyticAt_energy K) (energy_hasDerivAt_line K)
        (contDiff_kuramotoField K) (lipschitz_kuramotoField K) _
        (kuramotoField_twisted_eq K _) hst)

/-! ### Corollary 5.7: the role of six -/

/-- **Corollary 5.7.**  For `m ≠ 0`, the `m`-twisted state is linearly stable (every non-trivial
character is an eigenvector with a negative eigenvalue) iff `m` has order `6`. -/
theorem linearly_stable_iff {K : ℝ} (hK : 0 < K) {m : ZMod n} (hm : m ≠ 0) :
    (∀ k : ZMod n, k ≠ 0 → ∃ ev : ℝ, ev < 0 ∧ ∀ i, jac n K m (chi n k) i = (ev : ℂ) * chi n k i)
      ↔ addOrderOf m = 6 := by
  constructor
  · intro h
    by_contra h6
    obtain ⟨ev, hev, hjac⟩ := h m hm
    have h0 := hjac 0
    rw [chi_zero, mul_one] at h0
    by_cases h4 : addOrderOf m = 4
    · rw [(twisted_classification hK hm).2.1 h4] at h0
      have : ev = 0 := by exact_mod_cast h0.symm
      linarith
    · rw [jac_chi_self, chi_zero, mul_one] at h0
      have : K * g (addOrderOf m) = ev := by exact_mod_cast h0
      have := (twisted_unstable hK hm h4 h6).2
      linarith
  · intro h6 k hk
    obtain ⟨ev, hev, hjac⟩ := (twisted_classification hK hm).1 h6 k hk
    exact ⟨ev, by linarith, hjac⟩

/-- **Corollary 5.7.**  `X_n` has a non-zero twist of order `6` iff `6 ∣ n`. -/
theorem exists_order_six_iff : (∃ m : ZMod n, m ≠ 0 ∧ addOrderOf m = 6) ↔ 6 ∣ n := by
  constructor
  · rintro ⟨m, _, h⟩
    exact h ▸ addOrderOf_dvd_self m
  · intro h6
    exact ⟨_, natCast_div_ne_zero h6 (by norm_num), addOrderOf_natCast_div h6⟩

end ArithmeticDynamics

/-! ════════════════════════ Part 17: Circulant ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XVII: general circulant graphs `Cay(ℤ/n, S)` — the Kuramoto field, its Jacobian at twisted
states, the Fourier symbol, and the two criteria of Proposition 6.1.
-/

namespace ArithmeticDynamics

open Finset Real ComplexConjugate

variable {n : ℕ} [NeZero n]

/-- A symmetric connection set: `S = -S`. -/
def IsSymm (S : Finset (ZMod n)) : Prop := ∀ s ∈ S, -s ∈ S

omit [NeZero n] in
theorem sum_symm {β : Type*} [AddCommMonoid β] {S : Finset (ZMod n)} (hS : IsSymm S)
    (g : ZMod n → β) : ∑ s ∈ S, g (-s) = ∑ s ∈ S, g s :=
  Finset.sum_nbij' (fun s => -s) (fun s => -s) (fun s hs => hS s hs) (fun s hs => hS s hs)
    (fun s _ => neg_neg s) (fun s _ => neg_neg s) (fun s _ => rfl)

variable (S : Finset (ZMod n))

/-- The Kuramoto field on `Cay(ℤ/n, S)`. -/
noncomputable def cField (K : ℝ) (θ : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  K / (#S : ℝ) * ∑ s ∈ S, sin (θ (i + s) - θ i)

/-- The Laplacian of `Cay(ℤ/n, S)` on real vectors. -/
noncomputable def cLap (f : ZMod n → ℝ) (i : ZMod n) : ℝ := (#S : ℝ) * f i - ∑ s ∈ S, f (i + s)

/-- Edge weight `cos(2π m s/n)` at the `m`-twisted state. -/
noncomputable def cWeight (m s : ZMod n) : ℝ := (ZMod.stdAddChar (m * s) : ℂ).re

/-- The real Jacobian of the circulant Kuramoto field at the `m`-twisted state. -/
noncomputable def cJac (K : ℝ) (m : ZMod n) (f : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  K / (#S : ℝ) * ∑ s ∈ S, cWeight m s * (f (i + s) - f i)

/-- The (real) Fourier symbol `C_S(j) = ∑_{s∈S} cos(2π j s/n)`. -/
noncomputable def cSym (j : ZMod n) : ℝ := ∑ s ∈ S, cWeight j s

/-! ### Twisted states on a circulant -/

theorem twisted_diff_gen (a : ℕ) (i s : ZMod n) :
    twisted n a (i + s) - twisted n a i
      = 2 * π * (a * s.val : ℕ) / n - ((a * ((i.val + s.val) / n) : ℕ) : ℤ) * (2 * π) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hval : (((i + s).val : ℕ) : ℝ)
      = (i.val : ℝ) + (s.val : ℝ) - (n : ℝ) * (((i.val + s.val) / n : ℕ) : ℝ) := by
    have h := Nat.mod_add_div (i.val + s.val) n
    rw [← ZMod.val_add] at h
    have h' : (((i + s).val + n * ((i.val + s.val) / n) : ℕ) : ℝ)
        = ((i.val + s.val : ℕ) : ℝ) := by exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) h
    push_cast at h'
    linarith
  unfold twisted
  rw [hval, Int.cast_natCast]
  push_cast
  field_simp
  ring

theorem natCast_mul_val (a : ℕ) (s : ZMod n) :
    ((a : ℕ) : ZMod n) * s = ((a * s.val : ℕ) : ZMod n) := by
  push_cast
  rw [ZMod.natCast_zmod_val]

theorem cos_twisted_gen (a : ℕ) (i s : ZMod n) :
    cos (twisted n a (i + s) - twisted n a i) = cWeight (a : ZMod n) s := by
  rw [twisted_diff_gen, cos_sub_int_mul_two_pi, cWeight, natCast_mul_val, stdAddChar_natCast_re]

theorem sin_twisted_gen (a : ℕ) (i s : ZMod n) :
    sin (twisted n a (i + s) - twisted n a i) = (ZMod.stdAddChar ((a : ZMod n) * s) : ℂ).im := by
  rw [twisted_diff_gen, sin_sub_int_mul_two_pi, natCast_mul_val, stdAddChar_natCast_im]

variable {S}

/-- Twisted states are equilibria of the circulant Kuramoto model (`S` symmetric). -/
theorem cField_twisted (hS : IsSymm S) (K : ℝ) (a : ℕ) : cField S K (twisted n a) = 0 := by
  funext i
  unfold cField
  simp only [sin_twisted_gen, Pi.zero_apply]
  have h := sum_symm hS (fun s => (ZMod.stdAddChar ((a : ZMod n) * s) : ℂ).im)
  have hneg : ∀ s, (ZMod.stdAddChar ((a : ZMod n) * -s) : ℂ).im
      = -(ZMod.stdAddChar ((a : ZMod n) * s) : ℂ).im := by
    intro s
    rw [mul_neg, ← conj_stdAddChar, Complex.conj_im]
  simp only [hneg, sum_neg_distrib] at h
  have : ∑ s ∈ S, (ZMod.stdAddChar ((a : ZMod n) * s) : ℂ).im = 0 := by linarith
  rw [this, mul_zero]

/-- The circulant field has zero sum (`S` symmetric). -/
theorem sum_cField (hS : IsSymm S) (K : ℝ) (x : ZMod n → ℝ) : ∑ i, cField S K x i = 0 := by
  unfold cField
  rw [← mul_sum, sum_comm]
  have h1 : ∀ s : ZMod n, ∑ i : ZMod n, sin (x (i + s) - x i)
      = -∑ j : ZMod n, sin (x (j + -s) - x j) := by
    intro s
    rw [← Equiv.sum_comp (Equiv.subRight s), ← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [Equiv.subRight_apply, sub_add_cancel]
    rw [← sub_eq_add_neg, ← neg_sub (x (j - s)) (x j), sin_neg]
  have h2 := sum_symm hS (fun s => ∑ j : ZMod n, sin (x (j + s) - x j))
  rw [sum_congr rfl fun s _ => h1 s, sum_neg_distrib, h2]
  have : ∑ s ∈ S, ∑ j : ZMod n, sin (x (j + s) - x j) = 0 := by
    have e := sum_congr rfl fun s (_ : s ∈ S) => h1 s
    rw [sum_neg_distrib, h2] at e
    linarith
  rw [this, neg_zero, mul_zero]

theorem contDiff_cField (K : ℝ) : ContDiff ℝ 1 (cField S K) := by
  unfold cField
  fun_prop

theorem lipschitz_cField (K : ℝ) : ∃ L, LipschitzWith L (cField S K) := by
  refine ⟨⟨2 * |K|, by positivity⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hd : 0 ≤ dist x y := dist_nonneg
  show dist (cField S K x) (cField S K y) ≤ 2 * |K| * dist x y
  rw [dist_pi_le_iff (by positivity)]
  intro i
  rw [Real.dist_eq]
  unfold cField
  rw [← mul_sub, ← sum_sub_distrib, abs_mul]
  have hb : ∀ s : ZMod n, |sin (x (i + s) - x i) - sin (y (i + s) - y i)| ≤ 2 * dist x y := by
    intro s
    refine (abs_sin_sub_sin_le _ _).trans ?_
    have h1 : |x (i + s) - y (i + s)| ≤ dist x y := by
      rw [← Real.dist_eq]; exact dist_le_pi_dist x y _
    have h2 : |x i - y i| ≤ dist x y := by
      rw [← Real.dist_eq]; exact dist_le_pi_dist x y _
    calc |x (i + s) - x i - (y (i + s) - y i)| = |(x (i + s) - y (i + s)) - (x i - y i)| := by
          ring_nf
      _ ≤ |x (i + s) - y (i + s)| + |x i - y i| := abs_sub _ _
      _ ≤ 2 * dist x y := by linarith
  have hsum : |∑ s ∈ S, (sin (x (i + s) - x i) - sin (y (i + s) - y i))| ≤ #S * (2 * dist x y) := by
    calc |∑ s ∈ S, (sin (x (i + s) - x i) - sin (y (i + s) - y i))|
        ≤ ∑ s ∈ S, |sin (x (i + s) - x i) - sin (y (i + s) - y i)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ S, 2 * dist x y := sum_le_sum fun s _ => hb s
      _ = #S * (2 * dist x y) := by rw [sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos #S with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero, abs_zero, zero_mul]
    positivity
  · have hS0 : (0 : ℝ) < #S := by exact_mod_cast hpos
    rw [abs_div, abs_of_pos hS0]
    calc |K| / #S * |∑ s ∈ S, (sin (x (i + s) - x i) - sin (y (i + s) - y i))|
        ≤ |K| / #S * (#S * (2 * dist x y)) := by gcongr
      _ = 2 * |K| * dist x y := by field_simp

theorem fderiv_cField_twisted (K : ℝ) (a : ℕ) (f : ZMod n → ℝ) (i : ZMod n) :
    fderiv ℝ (cField S K) (twisted n a) f i = cJac S K (a : ZMod n) f i := by
  have hdiff : DifferentiableAt ℝ (cField S K) (twisted n a) :=
    (contDiff_cField K).differentiable one_ne_zero _
  have hline : HasDerivAt (fun t : ℝ => twisted n a + t • f) f 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const f).const_add (twisted n a)
    simpa using this
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hi := (hasDerivAt_pi.mp hcomp) i
  have hk : HasDerivAt (fun t : ℝ => (cField S K ∘ fun t => twisted n a + t • f) t i)
      (cJac S K (a : ZMod n) f i) 0 := by
    unfold cJac
    simp only [Function.comp_apply]
    unfold cField
    refine HasDerivAt.const_mul _ ?_
    refine HasDerivAt.fun_sum fun s _ => ?_
    have h1 : HasDerivAt (fun t : ℝ => (twisted n a + t • f) (i + s) - (twisted n a + t • f) i)
        (f (i + s) - f i) 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have ha := ((hasDerivAt_id (0 : ℝ)).mul_const (f (i + s))).const_add (twisted n a (i + s))
      have hb := ((hasDerivAt_id (0 : ℝ)).mul_const (f i)).const_add (twisted n a i)
      have := ha.fun_sub hb
      simpa using this
    have h2 := h1.sin
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero] at h2 ⊢
    rw [← cos_twisted_gen a i s]
    simpa [mul_comm] using h2
  exact hi.unique hk

/-! ### Spectrum of the Jacobian (complex form) -/

variable (S) in
/-- The Jacobian acting on complex vectors. -/
noncomputable def cJacC (K : ℝ) (m : ZMod n) (f : ZMod n → ℂ) (i : ZMod n) : ℂ :=
  ((K / (#S : ℝ) : ℝ) : ℂ) * ∑ s ∈ S, (cWeight m s : ℂ) * (f (i + s) - f i)

theorem cJacC_re (K : ℝ) (m : ZMod n) (f : ZMod n → ℂ) (i : ZMod n) :
    (cJacC S K m f i).re = cJac S K m (fun j => (f j).re) i := by
  unfold cJacC cJac
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [Complex.re_ofReal_mul, Complex.sub_re]

theorem cWeight_eq (m s : ZMod n) :
    (cWeight m s : ℂ)
      = ((ZMod.stdAddChar (m * s) : ℂ) + ZMod.stdAddChar (-(m * s))) / 2 := by
  unfold cWeight
  rw [Complex.re_eq_add_conj, AddChar.map_neg_eq_conj]

theorem cSym_eq (hS : IsSymm S) (j : ZMod n) :
    ((cSym S j : ℝ) : ℂ) = ∑ s ∈ S, (ZMod.stdAddChar (j * s) : ℂ) := by
  unfold cSym
  push_cast
  simp_rw [cWeight_eq, ← sum_div, sum_add_distrib]
  have := sum_symm hS (fun s => (ZMod.stdAddChar (j * s) : ℂ))
  simp only [mul_neg] at this
  rw [this]
  ring

theorem cSym_neg (hS : IsSymm S) (j : ZMod n) : cSym S (-j) = cSym S j := by
  unfold cSym cWeight
  have := sum_symm hS (fun s => (ZMod.stdAddChar (j * s) : ℂ).re)
  simp only [neg_mul, ← mul_neg] at this ⊢
  exact this

/-- **Lemma 5.2 (iii) for circulants.**  `J χ_k = (K/|S|) μ_k χ_k`,
`μ_k = (C(m+k) + C(m-k))/2 - C(m)`. -/
theorem cJacC_chi (hS : IsSymm S) (K : ℝ) (m k i : ZMod n) :
    cJacC S K m (chi n k) i
      = ((K / (#S : ℝ) * ((cSym S (m + k) + cSym S (m - k)) / 2 - cSym S m) : ℝ) : ℂ)
          * chi n k i := by
  have hterm : ∀ s : ZMod n, (cWeight m s : ℂ) * (chi n k (i + s) - chi n k i)
      = ((ZMod.stdAddChar ((m + k) * s) + ZMod.stdAddChar ((k - m) * s)) / 2
          - (ZMod.stdAddChar (m * s) + ZMod.stdAddChar (-m * s)) / 2) * chi n k i := by
    intro s
    have e1 : (m + k) * s = m * s + k * s := by ring
    have e2 : (k - m) * s = k * s + -(m * s) := by ring
    have e3 : -m * s = -(m * s) := by ring
    have e4 : k * (i + s) = k * i + k * s := by ring
    rw [cWeight_eq]
    unfold chi
    rw [e1, e2, e3, e4, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring
  unfold cJacC
  rw [sum_congr rfl fun s _ => hterm s, ← sum_mul]
  simp only [add_div, sum_sub_distrib, sum_add_distrib, ← sum_div]
  rw [← cSym_eq hS, ← cSym_eq hS, ← cSym_eq hS, ← cSym_eq hS]
  have h1 : cSym S (k - m) = cSym S (m - k) := by rw [← cSym_neg hS, neg_sub]
  have h2 : cSym S (-m) = cSym S m := cSym_neg hS m
  rw [h1, h2]
  push_cast
  ring

/-! ### Proposition 6.1 (i): an instability criterion -/

theorem cSym_zero : cSym S 0 = #S := by
  unfold cSym cWeight
  simp

theorem cWeight_ge (m s : ZMod n) : -1 ≤ cWeight m s := by
  unfold cWeight
  have h := Complex.abs_re_le_norm (ZMod.stdAddChar (m * s) : ℂ)
  have hn : ‖(ZMod.stdAddChar (m * s) : ℂ)‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  rw [hn] at h
  linarith [neg_abs_le (ZMod.stdAddChar (m * s) : ℂ).re]

theorem cWeight_le (m s : ZMod n) : cWeight m s ≤ 1 := by
  unfold cWeight
  have h := Complex.re_le_norm (ZMod.stdAddChar (m * s) : ℂ)
  have hn : ‖(ZMod.stdAddChar (m * s) : ℂ)‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  linarith

/-- **Proposition 6.1 (i).**  If `C(m) < (|S| + C(2m))/2`, then `Re χ_m` is a non-zero real
eigenvector of the Jacobian at the `m`-twisted state with positive eigenvalue. -/
theorem circulant_unstable_linear (hS : IsSymm S) {K : ℝ} (hK : 0 < K) (hSne : S.Nonempty)
    (m : ZMod n) (hcond : cSym S m < ((#S : ℝ) + cSym S (m + m)) / 2) :
    0 < K / (#S : ℝ) * (((#S : ℝ) + cSym S (m + m)) / 2 - cSym S m) ∧
      (fun j => (chi n m j).re) ≠ 0 ∧
      ∀ i, cJac S K m (fun j => (chi n m j).re) i
        = K / (#S : ℝ) * (((#S : ℝ) + cSym S (m + m)) / 2 - cSym S m) * (chi n m i).re := by
  have hS0 : (0 : ℝ) < #S := by exact_mod_cast hSne.card_pos
  refine ⟨mul_pos (by positivity) (by linarith), ?_, fun i => ?_⟩
  · intro h
    have := congrFun h 0
    simp [chi_zero] at this
  · have h := congrArg Complex.re (cJacC_chi hS K m m i)
    rw [cJacC_re, Complex.re_ofReal_mul, sub_self, cSym_zero] at h
    rw [h]
    ring

/-- **Proposition 6.1 (i), particular case.**  The hypothesis holds whenever `C(m) < 0`. -/
theorem circulant_cond_of_neg (m : ZMod n) (h : cSym S m < 0) :
    cSym S m < ((#S : ℝ) + cSym S (m + m)) / 2 := by
  have : -(#S : ℝ) ≤ cSym S (m + m) := by
    unfold cSym
    calc -(#S : ℝ) = ∑ s ∈ S, (-1 : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ s ∈ S, cWeight (m + m) s := sum_le_sum fun s _ => cWeight_ge _ _
  linarith

/-- **Proposition 6.1 (i), nonlinear form.** -/
theorem circulant_unstable (hI : LyapunovIndirectInstability n) (hS : IsSymm S) {K : ℝ}
    (hK : 0 < K) (hSne : S.Nonempty) (a : ℕ)
    (hcond : cSym S (a : ZMod n) < ((#S : ℝ) + cSym S ((a : ZMod n) + a)) / 2) :
    ¬ LyapunovStable (cField S K) (twisted n a) := by
  obtain ⟨hμ, hv, heig⟩ := circulant_unstable_linear hS hK hSne (a : ZMod n) hcond
  refine hI _ _ _ _ (contDiff_cField K) (lipschitz_cField K) (cField_twisted hS K a) hv ?_ hμ
  funext i
  rw [Pi.smul_apply, smul_eq_mul, fderiv_cField_twisted, heig]

/-! ### Proposition 6.1 (ii): a stability criterion -/

/-- The Dirichlet-form identity `∑_i ∑_s c_s (w_{i+s} - w_i) w_i = -(1/2) ∑_i ∑_s c_s (w_{i+s} - w_i)²`. -/
theorem dirichlet_identity (c : ZMod n → ℝ) (w : ZMod n → ℝ) :
    ∑ i : ZMod n, ∑ s ∈ S, c s * (w (i + s) - w i) * w i
      = -(1 / 2) * ∑ i : ZMod n, ∑ s ∈ S, c s * (w (i + s) - w i) ^ 2 := by
  have hshift : ∀ s : ZMod n, ∑ i : ZMod n, w (i + s) ^ 2 = ∑ i : ZMod n, w i ^ 2 := fun s => by
    have := Equiv.sum_comp (Equiv.addRight s) (fun i => w i ^ 2)
    simpa using this
  have e : ∀ i s, c s * (w (i + s) - w i) ^ 2
      = c s * w (i + s) ^ 2 - c s * w i ^ 2 - 2 * (c s * (w (i + s) - w i) * w i) := by
    intro i s; ring
  have h1 : ∑ i : ZMod n, ∑ s ∈ S, c s * w (i + s) ^ 2 = ∑ i : ZMod n, ∑ s ∈ S, c s * w i ^ 2 := by
    calc ∑ i : ZMod n, ∑ s ∈ S, c s * w (i + s) ^ 2
        = ∑ s ∈ S, ∑ i : ZMod n, c s * w (i + s) ^ 2 := sum_comm
      _ = ∑ s ∈ S, c s * ∑ i : ZMod n, w i ^ 2 := sum_congr rfl fun s _ => by rw [← mul_sum, hshift]
      _ = ∑ s ∈ S, ∑ i : ZMod n, c s * w i ^ 2 := sum_congr rfl fun s _ => by rw [mul_sum]
      _ = ∑ i : ZMod n, ∑ s ∈ S, c s * w i ^ 2 := sum_comm
  have hT : ∑ i : ZMod n, ∑ s ∈ S, c s * (w (i + s) - w i) ^ 2
      = ∑ i : ZMod n, ∑ s ∈ S, c s * w (i + s) ^ 2 - ∑ i : ZMod n, ∑ s ∈ S, c s * w i ^ 2
        - 2 * ∑ i : ZMod n, ∑ s ∈ S, c s * (w (i + s) - w i) * w i := by
    simp_rw [e, sum_sub_distrib, mul_sum]
  rw [hT, h1]
  ring

/-- **Proposition 6.1 (ii).**  If `S` generates `ℤ/n` and every edge weight at the `m`-twisted
state is positive, the Jacobian is negative definite on non-zero sum-zero vectors. -/
theorem circulant_stable_linear {K : ℝ} (hK : 0 < K)
    (hgen : AddSubgroup.closure (S : Set (ZMod n)) = ⊤) (m : ZMod n)
    (hpos : ∀ s ∈ S, 0 < cWeight m s) (w : ZMod n → ℝ) (hw : ∑ j, w j = 0) (hw0 : w ≠ 0) :
    ∑ j, cJac S K m w j * w j < 0 := by
  by_contra hcon
  push_neg at hcon
  -- every edge difference vanishes
  have hinv : ∀ s ∈ S, ∀ i, w (i + s) = w i := by
    rcases S.eq_empty_or_nonempty with hE | hSne
    · intro s hs; simp [hE] at hs
    have hS0 : (0 : ℝ) < #S := by exact_mod_cast hSne.card_pos
    have hform : ∑ j, cJac S K m w j * w j
        = K / (#S : ℝ) * (-(1 / 2) * ∑ i : ZMod n, ∑ s ∈ S, cWeight m s * (w (i + s) - w i) ^ 2) := by
      unfold cJac
      simp_rw [mul_assoc, ← mul_sum, sum_mul]
      rw [← dirichlet_identity (S := S) (cWeight m) w]
    have hnn : 0 ≤ ∑ i : ZMod n, ∑ s ∈ S, cWeight m s * (w (i + s) - w i) ^ 2 :=
      sum_nonneg fun i _ => sum_nonneg fun s hs => mul_nonneg (hpos s hs).le (sq_nonneg _)
    have hzero : ∑ i : ZMod n, ∑ s ∈ S, cWeight m s * (w (i + s) - w i) ^ 2 = 0 := by
      rw [hform] at hcon
      have : 0 < K / (#S : ℝ) := by positivity
      nlinarith
    intro s hs i
    have h1 := (sum_eq_zero_iff_of_nonneg fun i _ =>
      sum_nonneg fun s hs => mul_nonneg (hpos s hs).le (sq_nonneg _)).mp hzero i (mem_univ i)
    have h2 := (sum_eq_zero_iff_of_nonneg fun s hs =>
      mul_nonneg (hpos s hs).le (sq_nonneg (w (i + s) - w i))).mp h1 s hs
    have h3 : (w (i + s) - w i) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h (hpos s hs).ne'
      · exact h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
    linarith
  -- invariance under the generated subgroup
  have hall : ∀ g : ZMod n, ∀ i, w (i + g) = w i := by
    intro g
    have hg : g ∈ AddSubgroup.closure (S : Set (ZMod n)) := by rw [hgen]; trivial
    induction hg using AddSubgroup.closure_induction with
    | mem s hs => exact hinv s hs
    | zero => intro i; rw [add_zero]
    | add a b _ _ ha hb => intro i; rw [← add_assoc, hb, ha]
    | neg a _ ha =>
      intro i
      have := ha (i + -a)
      rw [neg_add_cancel_right] at this
      exact this.symm
  have hconst : ∀ g, w g = w 0 := fun g => by have := hall g 0; rwa [zero_add] at this
  have h0 : w 0 = 0 := by
    have : ∑ j : ZMod n, w j = n * w 0 := by
      rw [sum_congr rfl fun j _ => hconst j, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    rw [hw] at this
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hn
    · exact h
  exact hw0 (funext fun g => by rw [hconst g, h0]; rfl)

/-! ### Fourier symbol of the circulant Laplacian -/

theorem dft_cLap (hS : IsSymm S) (f : ZMod n → ℝ) (k : ZMod n) :
    ZMod.dft (fun x => (cLap S f x : ℂ)) k
      = ((((#S : ℝ) - cSym S k) : ℝ) : ℂ) * ZMod.dft (fun x => (f x : ℂ)) k := by
  rw [dft_eq, dft_eq]
  have hA : ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * ((∑ s ∈ S, f (i + s) : ℝ) : ℂ)
      = (∑ s ∈ S, (ZMod.stdAddChar (k * s) : ℂ)) * ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * (f i : ℂ) := by
    calc ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * ((∑ s ∈ S, f (i + s) : ℝ) : ℂ)
        = ∑ i : ZMod n, ∑ s ∈ S, ZMod.stdAddChar (-(i * k)) * ((f (i + s) : ℝ) : ℂ) := by
          push_cast; simp_rw [mul_sum]
      _ = ∑ s ∈ S, ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * ((f (i + s) : ℝ) : ℂ) := sum_comm
      _ = ∑ s ∈ S, (ZMod.stdAddChar (k * s) : ℂ)
            * ∑ i : ZMod n, ZMod.stdAddChar (-(i * k)) * (f i : ℂ) := by
          refine sum_congr rfl fun s _ => ?_
          rw [← Equiv.sum_comp (Equiv.subRight s)
            (fun i => ZMod.stdAddChar (-(i * k)) * ((f (i + s) : ℝ) : ℂ)), mul_sum]
          refine sum_congr rfl fun j _ => ?_
          have e : -((j - s) * k) = k * s + -(j * k) := by ring
          simp only [Equiv.subRight_apply, sub_add_cancel]
          rw [e, AddChar.map_add_eq_mul]
          ring
      _ = _ := by rw [sum_mul]
  have : ∀ i : ZMod n, ZMod.stdAddChar (-(i * k)) * ((cLap S f i : ℝ) : ℂ)
      = (#S : ℂ) * (ZMod.stdAddChar (-(i * k)) * (f i : ℂ))
        - ZMod.stdAddChar (-(i * k)) * ((∑ s ∈ S, f (i + s) : ℝ) : ℂ) := by
    intro i
    unfold cLap
    push_cast
    ring
  rw [sum_congr rfl fun i _ => this i, sum_sub_distrib, ← mul_sum, hA, ← cSym_eq hS]
  push_cast
  ring

theorem sum_cLap (f : ZMod n → ℝ) : ∑ j : ZMod n, cLap S f j = 0 := by
  unfold cLap
  rw [sum_sub_distrib, ← mul_sum, sum_comm]
  have : ∀ s : ZMod n, ∑ j : ZMod n, f (j + s) = ∑ j : ZMod n, f j := fun s =>
    Equiv.sum_comp (Equiv.addRight s) f
  rw [sum_congr rfl fun s _ => this s, sum_const, nsmul_eq_mul]
  ring

/-- Lower quadratic-form bound for the circulant Laplacian on sum-zero vectors. -/
theorem cLap_quad_lower (hS : IsSymm S) (f : ZMod n → ℝ) (hf : ∑ j, f j = 0) {c : ℝ}
    (hc : ∀ k : ZMod n, k ≠ 0 → c ≤ (#S : ℝ) - cSym S k) :
    c * sqNorm f ≤ ∑ j, cLap S f j * f j := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set F : ZMod n → ℂ := ZMod.dft (fun x => (f x : ℂ)) with hF
  have hP := plancherel (fun x => (cLap S f x : ℂ)) (fun x => (f x : ℂ))
  simp only [dft_cLap hS, Complex.conj_ofReal] at hP
  have hQ : (n : ℝ) * ∑ j, cLap S f j * f j
      = ∑ k, ((#S : ℝ) - cSym S k) * Complex.normSq (F k) := by
    have : ∀ k, (((#S : ℝ) - cSym S k : ℝ) : ℂ) * F k * conj (F k)
        = ((((#S : ℝ) - cSym S k) * Complex.normSq (F k) : ℝ) : ℂ) := by
      intro k
      rw [mul_assoc, Complex.mul_conj]
      push_cast
      ring
    simp only [← hF, this] at hP
    have h' : ((∑ k, ((#S : ℝ) - cSym S k) * Complex.normSq (F k) : ℝ) : ℂ)
        = (((n : ℝ) * ∑ j, cLap S f j * f j : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, hP]
      push_cast
      rfl
    exact_mod_cast h'.symm
  have hF0 : F 0 = 0 := dft_zero_of_sum_zero f hf
  have hN := sum_normSq_dft f
  rw [← hF] at hN
  have lo : ∀ k, c * Complex.normSq (F k) ≤ ((#S : ℝ) - cSym S k) * Complex.normSq (F k) := by
    intro k
    by_cases hk : k = 0
    · simp [hk, hF0]
    · exact mul_le_mul_of_nonneg_right (hc k hk) (Complex.normSq_nonneg _)
  have s1 := sum_le_sum fun k (_ : k ∈ (univ : Finset (ZMod n))) => lo k
  rw [← mul_sum, hN, ← hQ] at s1
  nlinarith

/-- For a generating set, every non-trivial Laplacian eigenvalue `|S| - C(k)` is positive. -/
theorem cLap_eig_pos (hgen : AddSubgroup.closure (S : Set (ZMod n)) = ⊤) (k : ZMod n)
    (hk : k ≠ 0) : 0 < (#S : ℝ) - cSym S k := by
  have hle : ∀ s ∈ S, cWeight k s ≤ 1 := fun s _ => cWeight_le k s
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ s ∈ S, (1 - cWeight k s) = 0 := by
    have h1 : 0 ≤ ∑ s ∈ S, (1 - cWeight k s) := sum_nonneg fun s hs => by linarith [hle s hs]
    have h2 : ∑ s ∈ S, (1 - cWeight k s) = (#S : ℝ) - cSym S k := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]; rfl
    linarith
  have hone : ∀ s ∈ S, (ZMod.stdAddChar (k * s) : ℂ) = 1 := by
    intro s hs
    have h := (sum_eq_zero_iff_of_nonneg fun s hs => by linarith [hle s hs]).mp hsum s hs
    have hre : (ZMod.stdAddChar (k * s) : ℂ).re = 1 := by unfold cWeight at h; linarith
    have hn : ‖(ZMod.stdAddChar (k * s) : ℂ)‖ = 1 := by
      rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
    have him : (ZMod.stdAddChar (k * s) : ℂ).im = 0 := by
      have := Complex.sq_norm (ZMod.stdAddChar (k * s) : ℂ)
      rw [hn, Complex.normSq_apply, hre] at this
      nlinarith [sq_nonneg (ZMod.stdAddChar (k * s) : ℂ).im]
    exact Complex.ext hre him
  have hall : ∀ g : ZMod n, (ZMod.stdAddChar (k * g) : ℂ) = 1 := by
    intro g
    have hg : g ∈ AddSubgroup.closure (S : Set (ZMod n)) := by rw [hgen]; trivial
    induction hg using AddSubgroup.closure_induction with
    | mem s hs => exact hone s hs
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add, AddChar.map_add_eq_mul, ha, hb, one_mul]
    | neg a _ ha => rw [mul_neg, AddChar.map_neg_eq_conj, ha, map_one]
  have h1 := hall 1
  rw [mul_one] at h1
  apply hk
  apply ZMod.injective_stdAddChar (N := n)
  rw [h1, AddChar.map_zero_eq_one]

end ArithmeticDynamics

/-! ════════════════════════ Part 18: GcdGraph ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XVIII: gcd graphs `X_n(D)` — symmetry, the hexagonal state (Proposition 6.2), the
decomposition (2.5) of the symbol into Ramanujan sums, integrality of the spectrum and the
rationality of the consensus rate (Proposition 6.3).
-/

namespace ArithmeticDynamics

open Finset Real ArithmeticFunction

variable {n : ℕ} [NeZero n]

/-- The connection set `S_D = {s : gcd(s, n) ∈ D}` of the gcd graph `X_n(D)`. -/
def gcdSet (n : ℕ) [NeZero n] (D : Finset ℕ) : Finset (ZMod n) :=
  univ.filter (fun s : ZMod n => Nat.gcd s.val n ∈ D)

theorem gcd_val_neg (s : ZMod n) : Nat.gcd (-s).val n = Nat.gcd s.val n := by
  rw [ZMod.neg_val]
  split_ifs with h
  · rw [h]; simp
  · exact Nat.gcd_self_sub_left (ZMod.val_lt s).le

theorem gcdSet_symm (D : Finset ℕ) : IsSymm (gcdSet n D) := by
  intro s hs
  simp only [gcdSet, mem_filter, mem_univ, true_and] at hs ⊢
  rwa [gcd_val_neg]

/-! ### Proposition 6.2: the hexagonal state on gcd graphs -/

theorem cWeight_hex_gcd (h6 : 6 ∣ n) {D : Finset ℕ} (hD6 : ∀ d ∈ D, Nat.Coprime d 6)
    {s : ZMod n} (hs : s ∈ gcdSet n D) : cWeight ((n / 6 : ℕ) : ZMod n) s = 1 / 2 := by
  simp only [gcdSet, mem_filter, mem_univ, true_and] at hs
  have hc := hD6 _ hs
  have h2 : ¬ (2 : ℤ) ∣ (s.val : ℤ) := by
    intro h
    have h' : 2 ∣ s.val := by exact_mod_cast h
    have : 2 ∣ Nat.gcd s.val n := Nat.dvd_gcd h' (dvd_trans (by norm_num) h6)
    have := Nat.Coprime.coprime_dvd_left this hc
    norm_num at this
  have h3 : ¬ (3 : ℤ) ∣ (s.val : ℤ) := by
    intro h
    have h' : 3 ∣ s.val := by exact_mod_cast h
    have : 3 ∣ Nat.gcd s.val n := Nat.dvd_gcd h' (dvd_trans (by norm_num) h6)
    have := Nat.Coprime.coprime_dvd_left this hc
    norm_num at this
  obtain ⟨t, ht⟩ := h6
  have ht0 : (t : ℝ) ≠ 0 := by
    have : t ≠ 0 := by rintro rfl; exact NeZero.ne n (by simpa using ht)
    exact_mod_cast this
  have hdiv : n / 6 = t := by rw [ht]; exact Nat.mul_div_cancel_left t (by norm_num)
  unfold cWeight
  rw [natCast_mul_val, stdAddChar_natCast_re, hdiv, ← cos_hexagonal _ h2 h3]
  congr 1
  have hn : (n : ℝ) = 6 * (t : ℝ) := by exact_mod_cast ht
  rw [hn]
  push_cast
  field_simp
  ring

/-- **Proposition 6.2, Jacobian.**  `J = -(K/(2|S_D|)) L_D` at the hexagonal state. -/
theorem cJac_hex_gcd (h6 : 6 ∣ n) {D : Finset ℕ} (hD6 : ∀ d ∈ D, Nat.Coprime d 6) (K : ℝ)
    (f : ZMod n → ℝ) (i : ZMod n) :
    cJac (gcdSet n D) K ((n / 6 : ℕ) : ZMod n) f i
      = -(K / (2 * (#(gcdSet n D) : ℝ))) * cLap (gcdSet n D) f i := by
  unfold cJac cLap
  rw [sum_congr rfl fun s hs => by rw [cWeight_hex_gcd h6 hD6 hs]]
  rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos #(gcdSet n D) with h0 | hpos
  · rw [h0]; simp
  · have : (#(gcdSet n D) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp
    ring

theorem cWeight_zero (s : ZMod n) : cWeight 0 s = 1 := by
  unfold cWeight
  simp

theorem cJac_sync (S : Finset (ZMod n)) (K : ℝ) (f : ZMod n → ℝ) (i : ZMod n) :
    cJac S K 0 f i = -(K / (#S : ℝ)) * cLap S f i := by
  unfold cJac cLap
  simp only [cWeight_zero, one_mul]
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  ring

theorem nonempty_of_gen (hn : 1 < n) {S : Finset (ZMod n)}
    (hgen : AddSubgroup.closure (S : Set (ZMod n)) = ⊤) : S.Nonempty := by
  rcases S.eq_empty_or_nonempty with h | h
  · exfalso
    haveI : Fact (1 < n) := ⟨hn⟩
    have h1 : (1 : ZMod n) ∈ AddSubgroup.closure (S : Set (ZMod n)) := by rw [hgen]; trivial
    rw [h, coe_empty, AddSubgroup.closure_empty, AddSubgroup.mem_bot] at h1
    exact one_ne_zero h1
  · exact h

/-- The algebraic connectivity `λ₂ = min_{k ≠ 0} (|S| - C(k))` of a circulant, for `n ≥ 2`. -/
noncomputable def lam2 (S : Finset (ZMod n)) (hn : 1 < n) : ℝ :=
  (univ.erase (0 : ZMod n)).inf'
    ⟨1, mem_erase.mpr ⟨by haveI : Fact (1 < n) := ⟨hn⟩; exact one_ne_zero, mem_univ _⟩⟩
    (fun k => (#S : ℝ) - cSym S k)

theorem lam2_le (S : Finset (ZMod n)) (hn : 1 < n) (k : ZMod n) (hk : k ≠ 0) :
    lam2 S hn ≤ (#S : ℝ) - cSym S k :=
  inf'_le _ (mem_erase.mpr ⟨hk, mem_univ _⟩)

theorem lam2_pos {S : Finset (ZMod n)} (hn : 1 < n)
    (hgen : AddSubgroup.closure (S : Set (ZMod n)) = ⊤) : 0 < lam2 S hn := by
  obtain ⟨k, hk, he⟩ := exists_mem_eq_inf' (s := univ.erase (0 : ZMod n))
    ⟨1, mem_erase.mpr ⟨by haveI : Fact (1 < n) := ⟨hn⟩; exact one_ne_zero, mem_univ _⟩⟩
    (fun k => (#S : ℝ) - cSym S k)
  unfold lam2
  rw [he]
  exact cLap_eig_pos hgen k (ne_of_mem_erase hk)

/-- **Proposition 6.2.**  If `6 ∣ n`, every `d ∈ D` is coprime to `6` and `X_n(D)` is connected,
the hexagonal state is exponentially stable modulo rotation with every rate below
`K λ₂(L_D)/(2|S_D|)`, and `λ₂(L_D) > 0`. -/
theorem gcd_hex_expStable (hL : LyapunovIndirectStability n) (h6 : 6 ∣ n) {D : Finset ℕ}
    (hD6 : ∀ d ∈ D, Nat.Coprime d 6)
    (hgen : AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) = ⊤)
    {K : ℝ} (hK : 0 < K) (hn : 1 < n) :
    0 < lam2 (gcdSet n D) hn ∧
      ∀ r', 0 < r' → r' < K * lam2 (gcdSet n D) hn / (2 * (#(gcdSet n D) : ℝ)) →
        ExpStableOnLevel (cField (gcdSet n D) K) (twisted n (n / 6)) r' := by
  set S := gcdSet n D
  have hlam := lam2_pos hn hgen
  have hSne := nonempty_of_gen hn hgen
  have hS0 : (0 : ℝ) < #S := by exact_mod_cast hSne.card_pos
  refine ⟨hlam, fun r' hr' hr => ?_⟩
  refine hL _ _ (K * lam2 S hn / (2 * #S)) (contDiff_cField K) (lipschitz_cField K)
    (cField_twisted (gcdSet_symm D) K _) (sum_cField (gcdSet_symm D) K) (by positivity)
    (fun w hw => ?_) r' hr' hr
  simp_rw [fderiv_cField_twisted, cJac_hex_gcd h6 hD6, mul_assoc, ← mul_sum]
  have hq := cLap_quad_lower (gcdSet_symm D) w hw (fun k hk => lam2_le S hn k hk)
  have hc : 0 ≤ K / (2 * (#S : ℝ)) := by positivity
  have := mul_le_mul_of_nonneg_left hq hc
  have e : K / (2 * (#S : ℝ)) * (lam2 S hn * sqNorm w) = K * lam2 S hn / (2 * #S) * sqNorm w := by
    field_simp
  linarith

/-- **Proposition 6.2, synchronous state.**  On a connected gcd graph the synchronous state is
exponentially stable modulo rotation with every rate below `K λ₂(L_D)/|S_D|` (twice the
hexagonal bound). -/
theorem gcd_sync_expStable (hL : LyapunovIndirectStability n) {D : Finset ℕ}
    (hgen : AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) = ⊤)
    {K : ℝ} (hK : 0 < K) (hn : 1 < n) :
    ∀ r', 0 < r' → r' < K * lam2 (gcdSet n D) hn / (#(gcdSet n D) : ℝ) →
      ExpStableOnLevel (cField (gcdSet n D) K) (twisted n 0) r' := by
  set S := gcdSet n D
  have hlam := lam2_pos hn hgen
  have hSne := nonempty_of_gen hn hgen
  have hS0 : (0 : ℝ) < #S := by exact_mod_cast hSne.card_pos
  intro r' hr' hr
  refine hL _ _ (K * lam2 S hn / #S) (contDiff_cField K) (lipschitz_cField K)
    (cField_twisted (gcdSet_symm D) K _) (sum_cField (gcdSet_symm D) K) (by positivity)
    (fun w hw => ?_) r' hr' hr
  simp_rw [fderiv_cField_twisted]
  have h0 : ((0 : ℕ) : ZMod n) = 0 := Nat.cast_zero
  rw [h0]
  simp_rw [cJac_sync, mul_assoc, ← mul_sum]
  have hq := cLap_quad_lower (gcdSet_symm D) w hw (fun k hk => lam2_le S hn k hk)
  have hc : 0 ≤ K / (#S : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hq hc
  have e : K / (#S : ℝ) * (lam2 S hn * sqNorm w) = K * lam2 S hn / #S * sqNorm w := by
    field_simp
  linarith

/-! ### Equation (2.5) and Proposition 6.3 -/

/-- **Equation (2.5).**  For `d ∣ n`, the sum of `e(ks/n)` over `gcd(s, n) = d` is the Ramanujan
sum `c_{n/d}(k)`. -/
theorem fiber_sum_eq_ramanujan {d : ℕ} (hd : d ∣ n) (hd0 : 0 < d) [NeZero (n / d)] (k : ZMod n) :
    ∑ s ∈ univ.filter (fun s : ZMod n => Nat.gcd s.val n = d), (ZMod.stdAddChar (k * s) : ℂ)
      = ramanujan (n / d) ((k.val : ℕ) : ZMod (n / d)) := by
  set N := n / d with hN
  have hnd : n = d * N := (Nat.mul_div_cancel' hd).symm
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hlt : ∀ x : ℕ, x < N → d * x < n := fun x hx =>
    lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_left hx hd0) hnd.symm
  have hgcd : ∀ x : ℕ, Nat.gcd (d * x) n = d * Nat.gcd x N := fun x => by
    rw [hnd, Nat.gcd_mul_left]
  have hndR : (n : ℝ) = d * N := by exact_mod_cast hnd
  unfold ramanujan
  symm
  refine sum_bij (fun t _ => ((d * (t : ZMod N).val : ℕ) : ZMod n)) ?_ ?_ ?_ ?_
  · intro t _
    simp only [mem_filter, mem_univ, true_and]
    rw [ZMod.val_natCast_of_lt (hlt _ (ZMod.val_lt _)), hgcd, ZMod.val_coe_unit_coprime, mul_one]
  · intro a _ b _ hab
    have := congrArg ZMod.val hab
    rw [ZMod.val_natCast_of_lt (hlt _ (ZMod.val_lt _)),
      ZMod.val_natCast_of_lt (hlt _ (ZMod.val_lt _))] at this
    exact Units.ext (ZMod.val_injective N (Nat.eq_of_mul_eq_mul_left hd0 this))
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    obtain ⟨t0, ht0⟩ : d ∣ s.val := hs ▸ Nat.gcd_dvd_left s.val n
    have ht0N : t0 < N := by
      have h1 := ZMod.val_lt s
      rw [ht0] at h1
      have h2 : d * t0 < d * N := lt_of_lt_of_eq h1 hnd
      exact Nat.lt_of_mul_lt_mul_left h2
    have hcop : Nat.Coprime t0 N := by
      have e : Nat.gcd (d * t0) n = d := by rw [← ht0]; exact hs
      rw [hgcd] at e
      have : d * Nat.gcd t0 N = d * 1 := by rw [e, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hd0 this
    refine ⟨ZMod.unitOfCoprime t0 hcop, mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt ht0N, ← ht0, ZMod.natCast_zmod_val]
  · intro t _
    have hk : k * ((d * (t : ZMod N).val : ℕ) : ZMod n)
        = ((k.val * (d * (t : ZMod N).val) : ℕ) : ZMod n) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hdiv : ((n / d : ℕ) : ℝ) = (n : ℝ) / d := Nat.cast_div hd hd'
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    have hreal : 2 * π * ((k.val * (t : ZMod (n / d)).val : ℕ) : ℝ) / ((n / d : ℕ) : ℝ)
        = 2 * π * ((k.val * (d * (t : ZMod (n / d)).val) : ℕ) : ℝ) / (n : ℝ) := by
      rw [hdiv]
      push_cast
      field_simp
    rw [natCast_mul_val, hk, stdAddChar_natCast, stdAddChar_natCast, hreal]

/-- Ramanujan sums are integers. -/
theorem ramanujan_int (N : ℕ) [NeZero N] (j : ZMod N) : ∃ z : ℤ, ramanujan N j = z := by
  set M := addOrderOf j
  have hM : 0 < M := addOrderOf_pos j
  have hdvd : Nat.totient M ∣ Nat.totient N :=
    Nat.totient_dvd_of_dvd (by have := addOrderOf_dvd_card (x := j); rwa [ZMod.card] at this)
  obtain ⟨c, hc⟩ := hdvd
  have hφM : (Nat.totient M : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hM).ne'
  refine ⟨c * moebius M, ?_⟩
  rw [ramanujan_eq, r, hc]
  have hMj : addOrderOf j = M := rfl
  rw [hMj]
  push_cast
  rw [mul_div_assoc', div_eq_iff hφM]
  ring

/-- **Integrality.**  Every value `C_{S_D}(k)` of the symbol of a gcd graph is an integer. -/
theorem cSym_gcd_int (D : Finset ℕ) (k : ZMod n) : ∃ z : ℤ, cSym (gcdSet n D) k = z := by
  have hsplit : ∑ s ∈ gcdSet n D, (ZMod.stdAddChar (k * s) : ℂ)
      = ∑ d ∈ D, ∑ s ∈ univ.filter (fun s : ZMod n => Nat.gcd s.val n = d),
          (ZMod.stdAddChar (k * s) : ℂ) := by
    rw [← sum_fiberwise_of_maps_to (s := gcdSet n D) (t := D) (g := fun s => Nat.gcd s.val n)
      (fun s hs => (mem_filter.mp hs).2)]
    refine sum_congr rfl fun d hd => ?_
    congr 1
    ext s
    simp only [gcdSet, mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hd, h⟩
  have hfib : ∀ d, ∃ z : ℤ, ∑ s ∈ univ.filter (fun s : ZMod n => Nat.gcd s.val n = d),
      (ZMod.stdAddChar (k * s) : ℂ) = z := by
    intro d
    by_cases hd : d ∣ n ∧ 0 < d
    · obtain ⟨hdn, hd0⟩ := hd
      haveI : NeZero (n / d) := ⟨by
        have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hdn) hd0
        omega⟩
      rw [fiber_sum_eq_ramanujan hdn hd0]
      exact ramanujan_int _ _
    · refine ⟨0, ?_⟩
      push_cast
      refine sum_eq_zero fun s hs => ?_
      exfalso
      simp only [mem_filter, mem_univ, true_and] at hs
      apply hd
      refine ⟨hs ▸ Nat.gcd_dvd_right _ _, ?_⟩
      rw [← hs]
      exact Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne n))
  choose z hz using hfib
  refine ⟨∑ d ∈ D, z d, ?_⟩
  have h := cSym_eq (gcdSet_symm D) k
  rw [hsplit, sum_congr rfl fun d _ => hz d] at h
  push_cast at h
  exact_mod_cast h

/-- **Proposition 6.3.**  On a connected gcd graph `X_n(D)`, with `C⁺ = max_{k≠0} C(k)` and
`C⁻ = min_{k≠0} C(k)`, the extreme Laplacian eigenvalues are `λ₂ = |S| - C⁺` and
`λ_max = |S| - C⁻`, the optimal rate is `(C⁺ - C⁻)/(2|S| - C⁺ - C⁻)`, and it is rational. -/
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
      ∃ q : ℚ, (Cp - Cm) / (2 * (#S : ℝ) - Cp - Cm) = q := by
  intro S ne Cp Cm
  obtain ⟨kp, hkp, hp⟩ := exists_mem_eq_sup' ne (cSym S)
  obtain ⟨km, hkm, hm⟩ := exists_mem_eq_inf' ne (cSym S)
  refine ⟨fun k hk => ⟨?_, ?_⟩, ⟨kp, ne_of_mem_erase hkp, hp.symm⟩,
    ⟨km, ne_of_mem_erase hkm, hm.symm⟩, by ring_nf, ?_⟩
  · have := le_sup' (cSym S) (mem_erase.mpr ⟨hk, mem_univ k⟩)
    linarith
  · have := inf'_le (cSym S) (mem_erase.mpr ⟨hk, mem_univ k⟩)
    linarith
  · obtain ⟨zp, hzp⟩ := cSym_gcd_int D kp
    obtain ⟨zm, hzm⟩ := cSym_gcd_int D km
    refine ⟨(zp - zm) / (2 * #S - zp - zm), ?_⟩
    simp only [Cp, Cm]
    rw [hp, hm, hzp, hzm]
    push_cast
    ring

end ArithmeticDynamics

/-! ════════════════════════ Part 19: Remarks ════════════════════════ -/

/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XIX: the mathematical content of the remarks — the set of values of `ρ*` (Remark 4.4),
the phase lags at hexagonal states (Remarks 5.8 and 6.4), the density bound (Remark 5.9),
and the quarter twists on gcd graphs (Remark 6.4).
-/

namespace ArithmeticDynamics

open Finset Real Filter Topology ArithmeticFunction

/-! ### Remark 4.4: the set of values of the optimal rate -/

/-- For fixed `p`, the rate `q/(2(p-1)(q-1)+q-2)` is strictly decreasing in `q`. -/
theorem rate_strictAnti_q {p q₁ q₂ : ℝ} (hp : 2 ≤ p) (hq : 3 ≤ q₁) (hlt : q₁ < q₂) :
    q₂ / (2 * (p - 1) * (q₂ - 1) + q₂ - 2) < q₁ / (2 * (p - 1) * (q₁ - 1) + q₁ - 2) := by
  have h1 := rate_denominator_pos hp hq
  have h2 := rate_denominator_pos hp (show 3 ≤ q₂ by linarith)
  rw [div_lt_div_iff₀ h2 h1]
  nlinarith

/-- For fixed `p`, the rate tends to `1/(2p-1)` as `q → ∞`, the value at the prime powers of `p`. -/
theorem rate_tendsto_q {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (fun q : ℝ => q / (2 * (p - 1) * (q - 1) + q - 2)) atTop (𝓝 (1 / (2 * p - 1))) := by
  have hA : 0 < 2 * p - 1 := by linarith
  have h : Tendsto (fun q : ℝ => 1 / ((2 * p - 1) - 2 * p / q)) atTop (𝓝 (1 / (2 * p - 1))) := by
    have h0 : Tendsto (fun q : ℝ => 2 * p / q) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := (tendsto_const_nhds (x := 2 * p - 1)).sub h0
    rw [sub_zero] at this
    exact (tendsto_const_nhds.div this hA.ne')
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with q hq
  have hq0 : q ≠ 0 := by linarith
  have hD := rate_denominator_pos hp hq
  have e : (2 * p - 1) - 2 * p / q = (2 * (p - 1) * (q - 1) + q - 2) / q := by
    field_simp
    ring
  rw [e, one_div_div]

/-- The prime-power values `1/(2p-1)` accumulate at `0`. -/
theorem rate_prime_pow_tendsto : Tendsto (fun p : ℝ => 1 / (2 * p - 1)) atTop (𝓝 0) := by
  have : Tendsto (fun p : ℝ => 2 * p - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (by norm_num))
  refine this.inv_tendsto_atTop.congr fun p => ?_
  simp [one_div]

/-- **Remark 4.4, even moduli.**  For even `n > 2`, `1/3 ≤ ρ*(X_n) ≤ 3/5`. -/
theorem rate_even {m : ℕ} (hm : 2 < m) (heven : 2 ∣ m) {ρ : ℝ} (h : IsRate m ρ) :
    1 / 3 ≤ ρ ∧ ρ ≤ 3 / 5 := by
  refine ⟨?_, (rate_le_and_eq_iff hm.le h).1⟩
  have hmin : m.minFac = 2 := (Nat.minFac_eq_two_iff m).mpr heven
  by_cases hpp : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
    have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow heven)).symm
    subst hp2
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have : k = 1 := by omega
      subst this
      omega
    rw [h.unique (isRate_prime_pow Nat.prime_two hk2)]
    norm_num
  · obtain ⟨q, hts⟩ := exists_twoSmallest hm.le hpp
    rw [h.unique (isRate_of_twoSmallest hm.le hts), hmin]
    have hq3 : (3 : ℝ) ≤ q := by
      have : 3 ≤ q := by have := hts.hlt; rw [hmin] at this; omega
      exact_mod_cast this
    have hD : (0 : ℝ) < 2 * (((2 : ℕ) : ℝ) - 1) * (q - 1) + q - 2 := by push_cast; linarith
    rw [le_div_iff₀ hD]
    push_cast
    linarith

/-- **Remark 4.4, odd moduli.**  For odd `n ≥ 3`, `ρ*(X_n) ≤ 5/19`, with equality iff `15 ∣ n`. -/
theorem rate_odd {m : ℕ} (hm : 2 ≤ m) (hodd : ¬ 2 ∣ m) {ρ : ℝ} (h : IsRate m ρ) :
    ρ ≤ 5 / 19 ∧ (ρ = 5 / 19 ↔ 15 ∣ m) := by
  have hmin3 : 3 ≤ m.minFac := by
    have hp := Nat.minFac_prime (show m ≠ 1 by omega)
    have h2 : m.minFac ≠ 2 := fun h2 => hodd (h2 ▸ Nat.minFac_dvd m)
    have := hp.two_le
    omega
  have h15 : ¬ 15 ∣ m → True := fun _ => trivial
  by_cases hpp : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
    have hminp : (p ^ k).minFac = p := Nat.Prime.pow_minFac hp (by omega)
    rw [hminp] at hmin3
    have hn15 : ¬ 15 ∣ p ^ k := by
      intro h15
      have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
      have h5 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hp).mp
        ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
      omega
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : k = 1 := by omega
      subst this
      rw [pow_one] at h hn15 ⊢
      rw [h.unique (isRate_prime hp)]
      exact ⟨by norm_num, by constructor <;> intro h' <;> [norm_num at h'; exact absurd h' hn15]⟩
    · rw [h.unique (isRate_prime_pow hp hk2)]
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hmin3
      have hlt : 1 / (2 * (p : ℝ) - 1) < 5 / 19 := by
        rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
        linarith
      exact ⟨hlt.le, by constructor <;> intro h' <;> [linarith; exact absurd h' hn15]⟩
  · obtain ⟨q, hts⟩ := exists_twoSmallest hm hpp
    rw [h.unique (isRate_of_twoSmallest hm hts)]
    set p := m.minFac with hpdef
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hmin3
    have hq5n : 5 ≤ q := by
      have hlt := hts.hlt
      have hq := hts.hq
      by_contra hq5
      have : q = 4 := by
        have := hq.two_le
        omega
      subst this
      exact absurd hq (by norm_num)
    have hq5 : (5 : ℝ) ≤ q := by exact_mod_cast hq5n
    have hD : (0 : ℝ) < 2 * ((p : ℝ) - 1) * ((q : ℝ) - 1) + q - 2 := by nlinarith
    have h0 : 0 ≤ ((p : ℝ) - 3) * ((q : ℝ) - 5) := mul_nonneg (by linarith) (by linarith)
    refine ⟨?_, ?_⟩
    · rw [div_le_div_iff₀ hD (by norm_num)]
      nlinarith
    · constructor
      · intro heq
        rw [div_eq_div_iff hD.ne' (by norm_num)] at heq
        have hp' : (p : ℝ) = 3 := by nlinarith
        have hq' : (q : ℝ) = 5 := by nlinarith
        have hpn : p = 3 := by exact_mod_cast hp'
        have hqn : q = 5 := by exact_mod_cast hq'
        have h3 : 3 ∣ m := by
          have e : m.minFac = 3 := hpn
          rw [← e]; exact Nat.minFac_dvd m
        have h5 : 5 ∣ m := by have := hts.hqn; rwa [hqn] at this
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5
      · intro h15
        have h3 : 3 ∣ m := dvd_trans (by norm_num) h15
        have h5 : 5 ∣ m := dvd_trans (by norm_num) h15
        have hpn : p = 3 := le_antisymm (hts.least 3 Nat.prime_three h3) hmin3
        have hqn : q = 5 :=
          le_antisymm (hts.second 5 (by norm_num) h5 (by omega)) hq5n
        rw [hpn, hqn]
        norm_num

/-! ### Remark 5.9: the density of `X_n` for `6 ∣ n` -/

/-- **Remark 5.9.**  If `6 ∣ n`, then `3 φ(n) ≤ n`, with equality iff the only prime divisors of
`n` are `2` and `3`. -/
theorem totient_le_third {m : ℕ} (hm0 : m ≠ 0) (h6 : 6 ∣ m) :
    3 * Nat.totient m ≤ m ∧ (3 * Nat.totient m = m ↔ m.primeFactors = {2, 3}) := by
  set P := m.primeFactors
  have h2P : 2 ∈ P := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (by norm_num) h6, hm0⟩
  have h3P : 3 ∈ P := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, dvd_trans (by norm_num) h6, hm0⟩
  set R := (P.erase 2).erase 3
  have hPR : P = insert 2 (insert 3 R) := by
    rw [insert_erase (mem_erase.mpr ⟨by norm_num, h3P⟩), insert_erase h2P]
  have h2R : 2 ∉ insert 3 R := by simp [R]
  have h3R : 3 ∉ R := by simp [R]
  have key : Nat.totient m * ∏ p ∈ P, p = m * ∏ p ∈ P, (p - 1) :=
    Nat.totient_mul_prod_primeFactors m
  rw [hPR, prod_insert h2R, prod_insert h3R, prod_insert h2R, prod_insert h3R] at key
  have hRpos : 0 < ∏ p ∈ R, p := prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (mem_of_mem_erase (mem_of_mem_erase hp))).pos
  have hle : ∏ p ∈ R, (p - 1) ≤ ∏ p ∈ R, p := prod_le_prod' fun p _ => Nat.sub_le p 1
  -- key : φ m * (2 * (3 * ∏ R p)) = m * ((2 - 1) * ((3 - 1) * ∏ R (p - 1)))
  norm_num at key
  have hmain : 3 * Nat.totient m * ∏ p ∈ R, p = m * ∏ p ∈ R, (p - 1) := by linarith
  constructor
  · have : 3 * Nat.totient m * ∏ p ∈ R, p ≤ m * ∏ p ∈ R, p := by
      rw [hmain]; exact Nat.mul_le_mul_left m hle
    exact Nat.le_of_mul_le_mul_right this hRpos
  · constructor
    · intro heq
      rw [heq] at hmain
      have hRR : ∏ p ∈ R, p = ∏ p ∈ R, (p - 1) :=
        Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) hmain
      have hRe : R = ∅ := by
        by_contra hne
        have hlt : ∏ p ∈ R, (p - 1) < ∏ p ∈ R, p := by
          refine prod_lt_prod_of_nonempty₀ (fun p hp => ?_) (fun p hp => ?_)
            (nonempty_iff_ne_empty.mpr hne)
          · have := (Nat.prime_of_mem_primeFactors (mem_of_mem_erase (mem_of_mem_erase hp))).two_le
            omega
          · have := (Nat.prime_of_mem_primeFactors (mem_of_mem_erase (mem_of_mem_erase hp))).two_le
            omega
        omega
      rw [hPR, hRe]
      rfl
    · intro hP
      have hRe : R = ∅ := by
        simp only [R, hP]
        decide
      rw [hRe, prod_empty, prod_empty, mul_one, mul_one] at hmain
      exact hmain

/-- **Remark 5.9.**  For `6 ∣ n`, the relative degree of `X_n` is below the `75%` density
threshold: `φ(n)/(n-1) < 3/4`. -/
theorem relative_degree_lt {m : ℕ} (hm0 : m ≠ 0) (h6 : 6 ∣ m) :
    (Nat.totient m : ℝ) / ((m : ℝ) - 1) < 3 / 4 := by
  have hm6 : 6 ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h6
  have h := (totient_le_third hm0 h6).1
  have hm : (6 : ℝ) ≤ m := by exact_mod_cast hm6
  have h' : 3 * (Nat.totient m : ℝ) ≤ m := by exact_mod_cast h
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-! ### Remarks 5.8 and 6.4: phase lags at the hexagonal state -/

/-- The phase lag `π s/3` across an edge of step `s` at the hexagonal state has cosine `1`, `1/2`,
`-1/2` or `-1` according to `gcd(s, 6) = 6, 1, 2, 3`. -/
theorem cos_hex_cases (s : ℤ) :
    (6 ∣ s → cos (π * s / 3) = 1) ∧
    (¬ 2 ∣ s → ¬ 3 ∣ s → cos (π * s / 3) = 1 / 2) ∧
    (2 ∣ s → ¬ 3 ∣ s → cos (π * s / 3) = -1 / 2) ∧
    (¬ 2 ∣ s → 3 ∣ s → cos (π * s / 3) = -1) := by
  refine ⟨fun h => ?_, fun h2 h3 => cos_hexagonal s h2 h3, fun h2 h3 => ?_, fun h2 h3 => ?_⟩
  · obtain ⟨k, rfl⟩ := h
    have : π * ((6 * k : ℤ) : ℝ) / 3 = (k : ℝ) * (2 * π) := by push_cast; ring
    rw [this, cos_int_mul_two_pi]
  · have hk : ∃ k : ℤ, s = 6 * k + 2 ∨ s = 6 * k - 2 := by
      have : s % 6 = 2 ∨ s % 6 = 4 := by omega
      rcases this with h | h
      · exact ⟨s / 6, Or.inl (by omega)⟩
      · exact ⟨s / 6 + 1, Or.inr (by omega)⟩
    obtain ⟨k, rfl | rfl⟩ := hk
    · have : π * ((6 * k + 2 : ℤ) : ℝ) / 3 = 2 * π / 3 + (k : ℝ) * (2 * π) := by push_cast; ring
      rw [this, cos_add_int_mul_two_pi]
      have : 2 * π / 3 = π - π / 3 := by ring
      rw [this, cos_pi_sub, cos_pi_div_three]
      ring
    · have : π * ((6 * k - 2 : ℤ) : ℝ) / 3 = -(2 * π / 3) + (k : ℝ) * (2 * π) := by push_cast; ring
      rw [this, cos_add_int_mul_two_pi, cos_neg]
      have : 2 * π / 3 = π - π / 3 := by ring
      rw [this, cos_pi_sub, cos_pi_div_three]
      ring
  · have hk : ∃ k : ℤ, s = 6 * k + 3 := ⟨s / 6, by omega⟩
    obtain ⟨k, rfl⟩ := hk
    have : π * ((6 * k + 3 : ℤ) : ℝ) / 3 = π + (k : ℝ) * (2 * π) := by push_cast; ring
    rw [this, cos_add_int_mul_two_pi, cos_pi]

variable {n : ℕ} [NeZero n]

/-- **Remark 6.4, quarter twists on gcd graphs.**  If `4 ∣ n` and every element of `D` is odd,
every edge weight at the quarter twist `m = n/4` of `X_n(D)` vanishes, hence so does the
Jacobian. -/
theorem cWeight_quarter_gcd (h4 : 4 ∣ n) {D : Finset ℕ} (hDodd : ∀ d ∈ D, Odd d)
    {s : ZMod n} (hs : s ∈ gcdSet n D) : cWeight ((n / 4 : ℕ) : ZMod n) s = 0 := by
  simp only [gcdSet, mem_filter, mem_univ, true_and] at hs
  have hodd : ¬ 2 ∣ s.val := by
    intro h
    have : 2 ∣ Nat.gcd s.val n := Nat.dvd_gcd h (dvd_trans (by norm_num) h4)
    obtain ⟨j, hj⟩ := hDodd _ hs
    omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (s.val : ℤ) = 2 * k + 1 := ⟨(s.val : ℤ) / 2, by omega⟩
  obtain ⟨t, ht⟩ := h4
  have ht0 : (t : ℝ) ≠ 0 := by
    have : t ≠ 0 := by rintro rfl; exact NeZero.ne n (by simpa using ht)
    exact_mod_cast this
  have hdiv : n / 4 = t := by rw [ht]; exact Nat.mul_div_cancel_left t (by norm_num)
  unfold cWeight
  rw [natCast_mul_val, stdAddChar_natCast_re, hdiv, ← cos_quarter k]
  congr 1
  have hn : (n : ℝ) = 4 * (t : ℝ) := by exact_mod_cast ht
  have hv : ((s.val : ℕ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by exact_mod_cast hk
  rw [hn]
  push_cast
  push_cast at hv
  rw [hv]
  field_simp
  ring

theorem cJac_quarter_gcd (h4 : 4 ∣ n) {D : Finset ℕ} (hDodd : ∀ d ∈ D, Odd d) (K : ℝ)
    (f : ZMod n → ℝ) (i : ZMod n) : cJac (gcdSet n D) K ((n / 4 : ℕ) : ZMod n) f i = 0 := by
  unfold cJac
  rw [sum_eq_zero fun s hs => by rw [cWeight_quarter_gcd h4 hDodd hs, zero_mul], mul_zero]

/-- **Lemma 5.3.**  `g(1) = 0`. -/
theorem g_one : g 1 = 0 := by
  unfold g
  norm_num [r_one]

end ArithmeticDynamics
