/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part VII: twisted states of the Kuramoto model on `X_n` (Section 5 of the paper):
equilibria, the Jacobian and its spectrum, and the classification by additive order.
-/
import Mathlib
import ArithmeticDynamics.Kuramoto
import ArithmeticDynamics.Spectrum

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
