/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part X: Fourier analysis on `ℤ/n` — orthogonality, Plancherel, and the Laplacian of `X_n`
as a Fourier multiplier; quadratic-form and contraction bounds on sum-zero vectors.
-/
import Mathlib
import ArithmeticDynamics.Classification

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
