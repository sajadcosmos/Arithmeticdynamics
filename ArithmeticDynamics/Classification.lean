/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part VIII: completeness of the character spectrum, the natural-step bound
(Proposition 4.7) and the classification theorem for twisted states (Theorem 5.4).
-/
import Mathlib
import ArithmeticDynamics.Twisted

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
