/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part I: the algebra behind the optimal consensus rate (Section 4 of the paper).

All statements are division-free: a quotient `x = u / v` is encoded by the
hypothesis `x * v = u`.  This keeps every proof inside `linear_combination`
and `nlinarith`.
-/
import Mathlib

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
