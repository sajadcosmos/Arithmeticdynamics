/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XVII: general circulant graphs `Cay(ℤ/n, S)` — the Kuramoto field, its Jacobian at twisted
states, the Fourier symbol, and the two criteria of Proposition 6.1.
-/
import Mathlib
import ArithmeticDynamics.Nonlinear

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
