/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part II: the trigonometric core of the Kuramoto results (Section 5 of the paper).
-/
import Mathlib

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
