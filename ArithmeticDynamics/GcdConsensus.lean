/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XX: consensus on general circulants and on gcd graphs (Proposition 6.4 and Example 6.5).

* the iteration `x ↦ (I - ε L_S) x` on an arbitrary symmetric circulant `Cay(ℤ/n, S)`,
  with the spectral contraction estimate and the exact decay of each Fourier mode;
* connected case: with the optimal step the error contracts at the rate
  `ρ* = (λ_max - λ₂)/(λ_max + λ₂) < 1`, so consensus occurs, and no constant step does better;
* disconnected case: `λ₂ = 0` and a non-constant vector is fixed by every step, so consensus
  fails from that initial condition;
* for gcd graphs `X_n(D)` with `D` a set of proper divisors: connectivity is equivalent to
  `gcd(D) = 1`, and the two cases above are stated with `C⁺ = max_{k≠0} C(k)`,
  `C⁻ = min_{k≠0} C(k)`;
* the example `n = 6`, `D = {2}` (two disjoint triangles).
-/
import Mathlib
import ArithmeticDynamics.GcdGraph
import ArithmeticDynamics.ConsensusDynamics

namespace ArithmeticDynamics

open Finset Filter Topology

variable {n : ℕ} [NeZero n]

/-! ### The consensus iteration on a circulant -/

/-- One step of the consensus iteration `x ↦ (I - ε L_S) x` on `Cay(ℤ/n, S)`. -/
noncomputable def cStep (S : Finset (ZMod n)) (ε : ℝ) (x : ZMod n → ℝ) : ZMod n → ℝ :=
  fun j => x j - ε * cLap S x j

variable {S : Finset (ZMod n)}

omit [NeZero n] in
theorem cLap_sub_const (x : ZMod n → ℝ) (c : ℝ) :
    cLap S (fun j => x j - c) = cLap S x := by
  funext i
  unfold cLap
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  ring

omit [NeZero n] in
theorem cLap_smul (x : ZMod n → ℝ) (c : ℝ) :
    cLap S (fun j => c * x j) = fun j => c * cLap S x j := by
  funext i
  unfold cLap
  rw [← mul_sum]
  ring

theorem sum_cStep (ε : ℝ) (x : ZMod n → ℝ) : ∑ j, cStep S ε x j = ∑ j, x j := by
  unfold cStep
  rw [sum_sub_distrib, ← mul_sum, sum_cLap, mul_zero, sub_zero]

theorem avg_cStep (ε : ℝ) (x : ZMod n → ℝ) : avg (cStep S ε x) = avg x := by
  unfold avg
  rw [sum_cStep]

theorem err_cStep (ε : ℝ) (x : ZMod n → ℝ) : err (cStep S ε x) = cStep S ε (err x) := by
  funext j
  unfold err
  rw [avg_cStep]
  unfold cStep
  rw [cLap_sub_const]
  ring

/-- **Spectral contraction on a circulant.**  If `|1 - ε (|S| - C(k))| ≤ ρ` for every `k ≠ 0`,
then on sum-zero vectors one step contracts the squared norm by `ρ²`. -/
theorem sqNorm_cStep_le (hS : IsSymm S) (f : ZMod n → ℝ) (hf : ∑ j, f j = 0) {ε ρ : ℝ}
    (hρ : ∀ k : ZMod n, k ≠ 0 → |1 - ε * ((#S : ℝ) - cSym S k)| ≤ ρ) :
    sqNorm (cStep S ε f) ≤ ρ ^ 2 * sqNorm f := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set g : ZMod n → ℝ := cStep S ε f with hg
  have hdft : ∀ k, ZMod.dft (fun x => (g x : ℂ)) k
      = ((1 - ε * ((#S : ℝ) - cSym S k) : ℝ) : ℂ) * ZMod.dft (fun x => (f x : ℂ)) k := by
    intro k
    have e : (fun x => (g x : ℂ))
        = (fun x => (f x : ℂ)) - (ε : ℂ) • (fun x => (cLap S f x : ℂ)) := by
      funext x
      simp only [hg, cStep, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, dft_cLap hS, smul_eq_mul]
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
      have h2 : (1 - ε * ((#S : ℝ) - cSym S k)) * (1 - ε * ((#S : ℝ) - cSym S k)) ≤ ρ ^ 2 := by
        rw [← sq, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      exact mul_le_mul_of_nonneg_right h2 (Complex.normSq_nonneg _)
  have hsum := sum_le_sum fun k (_ : k ∈ (univ : Finset (ZMod n))) => key k
  rw [← mul_sum, sum_normSq_dft, sum_normSq_dft] at hsum
  have : (n : ℝ) * sqNorm g ≤ (n : ℝ) * (ρ ^ 2 * sqNorm f) := by linarith
  exact le_of_mul_le_mul_left this hn

/-- Iterated form: `‖x(t) - x̄ 1‖² ≤ ρ^{2t} ‖x(0) - x̄ 1‖²`. -/
theorem sqNorm_err_cIterate (hS : IsSymm S) {ε ρ : ℝ}
    (hρ : ∀ k : ZMod n, k ≠ 0 → |1 - ε * ((#S : ℝ) - cSym S k)| ≤ ρ)
    (x : ZMod n → ℝ) (t : ℕ) :
    sqNorm (err ((cStep S ε)^[t] x)) ≤ (ρ ^ 2) ^ t * sqNorm (err x) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', err_cStep, pow_succ]
    calc sqNorm (cStep S ε (err ((cStep S ε)^[t] x)))
        ≤ ρ ^ 2 * sqNorm (err ((cStep S ε)^[t] x)) := sqNorm_cStep_le hS _ (sum_err _) hρ
      _ ≤ ρ ^ 2 * ((ρ ^ 2) ^ t * sqNorm (err x)) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = (ρ ^ 2) ^ t * ρ ^ 2 * sqNorm (err x) := by ring

/-! ### Exact decay of a single Fourier mode -/

/-- The real Fourier mode `x_j = cos(2π k j/n)`. -/
noncomputable def cosMode (k : ZMod n) : ZMod n → ℝ := fun j => cWeight k j

theorem cLap_cosMode (hS : IsSymm S) (k : ZMod n) :
    cLap S (cosMode k) = fun j => ((#S : ℝ) - cSym S k) * cosMode k j := by
  funext j
  have h : ∑ s ∈ S, (ZMod.stdAddChar (k * (j + s)) : ℂ)
      = (cSym S k : ℂ) * ZMod.stdAddChar (k * j) := by
    rw [cSym_eq hS, sum_mul]
    refine sum_congr rfl fun s _ => ?_
    rw [mul_add, AddChar.map_add_eq_mul, mul_comm]
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, Complex.re_ofReal_mul] at hre
  unfold cLap cosMode
  change (#S : ℝ) * cWeight k j - ∑ s ∈ S, (ZMod.stdAddChar (k * (j + s)) : ℂ).re = _
  rw [hre]
  unfold cWeight
  ring

theorem sum_cosMode {k : ZMod n} (hk : k ≠ 0) : ∑ j, cosMode k j = 0 := by
  have h := sum_stdAddChar_mul (n := n) k
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' hk)] at h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, Complex.zero_re] at hre
  unfold cosMode cWeight
  simpa [mul_comm] using hre

theorem cosMode_zero (k : ZMod n) : cosMode k 0 = 1 := by
  unfold cosMode cWeight
  simp

theorem err_cosMode {k : ZMod n} (hk : k ≠ 0) : err (cosMode k) = cosMode k := by
  funext j
  unfold err avg
  rw [sum_cosMode hk]
  simp

theorem cIterate_cosMode (hS : IsSymm S) (k : ZMod n) (ε : ℝ) (t : ℕ) :
    (cStep S ε)^[t] (cosMode k) = fun j => (1 - ε * ((#S : ℝ) - cSym S k)) ^ t * cosMode k j := by
  induction t with
  | zero => funext j; simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    funext j
    unfold cStep
    rw [cLap_smul, cLap_cosMode hS]
    ring

theorem sqNorm_smul (c : ℝ) (x : ZMod n → ℝ) : sqNorm (fun j => c * x j) = c ^ 2 * sqNorm x := by
  unfold sqNorm
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- **Exactness of a mode.**  For `k ≠ 0` the real mode `cos(2π k j/n)` is a non-constant initial
vector whose consensus error decays exactly by the factor `|1 - ε(|S| - C(k))|` per step. -/
theorem circulant_mode_exact (hS : IsSymm S) {k : ZMod n} (hk : k ≠ 0) (ε : ℝ) :
    err (cosMode k) ≠ 0 ∧ ∀ t : ℕ,
      sqNorm (err ((cStep S ε)^[t] (cosMode k)))
        = ((1 - ε * ((#S : ℝ) - cSym S k)) ^ 2) ^ t * sqNorm (err (cosMode k)) := by
  refine ⟨?_, fun t => ?_⟩
  · rw [err_cosMode hk]
    intro h
    have := congrFun h 0
    rw [cosMode_zero] at this
    exact one_ne_zero this
  · have hsum : ∑ j, ((cStep S ε)^[t] (cosMode k)) j = 0 := by
      rw [cIterate_cosMode hS, ← mul_sum, sum_cosMode hk, mul_zero]
    have herr : err ((cStep S ε)^[t] (cosMode k)) = (cStep S ε)^[t] (cosMode k) := by
      funext j
      unfold err avg
      rw [hsum]
      simp
    rw [herr, err_cosMode hk, cIterate_cosMode hS, sqNorm_smul, ← pow_mul, ← pow_mul, mul_comm 2 t]

/-! ### Connected circulants -/

/-- **Consensus on a circulant with spectral bounds `0 < a ≤ λ(k) ≤ b` (`k ≠ 0`).**  With the
step `ε* = 2/(a+b)` the error contracts at rate `ρ = (b-a)/(a+b) < 1` and tends to zero. -/
theorem circulant_consensus (hS : IsSymm S) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hk : ∀ k : ZMod n, k ≠ 0 → a ≤ (#S : ℝ) - cSym S k ∧ (#S : ℝ) - cSym S k ≤ b) :
    0 ≤ (b - a) / (a + b) ∧ (b - a) / (a + b) < 1 ∧
    ∀ x : ZMod n → ℝ,
      (∀ t : ℕ, sqNorm (err ((cStep S (2 / (a + b)))^[t] x))
          ≤ (((b - a) / (a + b)) ^ 2) ^ t * sqNorm (err x)) ∧
      Tendsto (fun t : ℕ => sqNorm (err ((cStep S (2 / (a + b)))^[t] x))) atTop (𝓝 0) := by
  have hs : 0 < a + b := by linarith
  have hρ0 : 0 ≤ (b - a) / (a + b) := div_nonneg (by linarith) hs.le
  have hρ1 : (b - a) / (a + b) < 1 := by
    rw [div_lt_one hs]; linarith
  refine ⟨hρ0, hρ1, fun x => ?_⟩
  have hbound : ∀ t : ℕ, sqNorm (err ((cStep S (2 / (a + b)))^[t] x))
      ≤ (((b - a) / (a + b)) ^ 2) ^ t * sqNorm (err x) := by
    refine sqNorm_err_cIterate hS (fun k hk' => ?_) x
    exact contraction_of_opt_step hs (by field_simp) (by field_simp) (hk k hk').1 (hk k hk').2
  refine ⟨hbound, ?_⟩
  have hq0 : 0 ≤ ((b - a) / (a + b)) ^ 2 := sq_nonneg _
  have hq1 : ((b - a) / (a + b)) ^ 2 < 1 := by
    have := pow_lt_pow_left₀ hρ1 hρ0 (two_ne_zero)
    simpa using this
  have hlim : Tendsto (fun t : ℕ => (((b - a) / (a + b)) ^ 2) ^ t * sqNorm (err x)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (sqNorm (err x))
  exact squeeze_zero (fun t => sqNorm_nonneg _) hbound hlim

/-! ### Disconnected circulants -/

/-- The indicator of the subgroup `g ℤ/n`. -/
noncomputable def subIndicator (n : ℕ) [NeZero n] (g : ℕ) : ZMod n → ℝ :=
  fun j => if g ∣ j.val then 1 else 0

theorem dvd_val_add_iff {g : ℕ} (hgn : g ∣ n) {i s : ZMod n} (hs : g ∣ s.val) :
    g ∣ (i + s).val ↔ g ∣ i.val := by
  rw [ZMod.val_add, Nat.dvd_mod_iff hgn]
  exact (Nat.dvd_add_left hs)

theorem cLap_subIndicator {g : ℕ} (hgn : g ∣ n) (hgS : ∀ s ∈ S, g ∣ s.val) :
    cLap S (subIndicator n g) = 0 := by
  funext i
  unfold cLap
  have : ∀ s ∈ S, subIndicator n g (i + s) = subIndicator n g i := by
    intro s hs
    unfold subIndicator
    simp only [dvd_val_add_iff hgn (hgS s hs)]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  simp

theorem err_subIndicator_ne (hn : 1 < n) {g : ℕ} (hg1 : 1 < g) :
    err (subIndicator n g) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have : Fact (1 < n) := ⟨hn⟩
  have v1 : (1 : ZMod n).val = 1 := ZMod.val_one n
  have nd : ¬ g ∣ 1 := fun hd => by have := Nat.le_of_dvd one_pos hd; omega
  unfold err subIndicator at h0 h1
  simp only [ZMod.val_zero, dvd_zero, ite_true, v1, nd, ite_false, Pi.zero_apply] at h0 h1
  linarith

theorem cSym_le (k : ZMod n) : cSym S k ≤ #S := by
  unfold cSym
  calc ∑ s ∈ S, cWeight k s ≤ ∑ _s ∈ S, (1 : ℝ) := sum_le_sum fun s _ => cWeight_le k s
    _ = #S := by simp

theorem lam2_nonneg (hn : 1 < n) : 0 ≤ lam2 S hn := by
  unfold lam2
  exact (le_inf'_iff _ _).mpr fun k _ => by linarith [cSym_le (S := S) k]

/-- **No consensus on a disconnected circulant.**  If every element of `S` lies in the proper
subgroup `g ℤ/n` (`1 < g ∣ n`), then `λ₂ = 0`, and the indicator of that subgroup is a
non-constant vector fixed by every step of the iteration, so its consensus error never decays. -/
theorem circulant_no_consensus (hS : IsSymm S) (hn : 1 < n) {g : ℕ} (hg1 : 1 < g)
    (hgn : g ∣ n) (hgS : ∀ s ∈ S, g ∣ s.val) :
    lam2 S hn = 0 ∧ err (subIndicator n g) ≠ 0 ∧
      ∀ (ε : ℝ) (t : ℕ), (cStep S ε)^[t] (subIndicator n g) = subIndicator n g := by
  have hfix : ∀ (ε : ℝ), cStep S ε (subIndicator n g) = subIndicator n g := by
    intro ε
    funext j
    unfold cStep
    rw [cLap_subIndicator hgn hgS]
    simp
  have hne := err_subIndicator_ne hn hg1
  refine ⟨?_, hne, fun ε t => Function.iterate_fixed (hfix ε) t⟩
  refine le_antisymm ?_ (lam2_nonneg hn)
  by_contra hpos
  rw [not_le] at hpos
  set f := err (subIndicator n g) with hf
  have hq := cLap_quad_lower hS f (sum_err _) (c := lam2 S hn) fun k hk => lam2_le S hn k hk
  have hz : ∑ j, cLap S f j * f j = 0 := by
    rw [hf]
    unfold err
    rw [cLap_sub_const, cLap_subIndicator hgn hgS]
    simp
  rw [hz] at hq
  have hsq : 0 < sqNorm f := by
    rcases (sqNorm_nonneg f).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hne
      funext j
      have hzero := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (f j))).mp h.symm j (mem_univ _)
      simpa using hzero
  nlinarith

/-- `λ₂ > 0` exactly when `S` generates `ℤ/n`, i.e. when the circulant is connected. -/
theorem lam2_pos_iff (hS : IsSymm S) (hn : 1 < n) :
    0 < lam2 S hn ↔ AddSubgroup.closure (S : Set (ZMod n)) = ⊤ := by
  constructor
  · intro hpos
    by_contra htop
    -- the subgroup generated by `S` is `g ℤ/n` for a divisor `1 < g ∣ n`
    set H := AddSubgroup.closure (S : Set (ZMod n)) with hH
    -- take `g` the additive order of a generator of the quotient: use `g = n / |H|`
    obtain ⟨g, hg1, hgn, hgS⟩ : ∃ g : ℕ, 1 < g ∧ g ∣ n ∧ ∀ s ∈ S, g ∣ s.val := by
      -- `H` is cyclic, generated by some `h`; then `g = gcd(h.val, n)` works
      obtain ⟨h, hh⟩ := IsAddCyclic.exists_generator (α := H)
      set g := Nat.gcd (h : ZMod n).val n with hgdef
      have hgn : g ∣ n := Nat.gcd_dvd_right _ _
      have hmem : ∀ x ∈ H, g ∣ x.val := by
        intro x hx
        obtain ⟨m, hm⟩ := hh ⟨x, hx⟩
        have hx' : x = m • (h : ZMod n) := by
          have := congrArg Subtype.val hm
          simpa using this.symm
        rw [hx', zsmul_eq_mul, ZMod.val_mul, Nat.dvd_mod_iff hgn]
        exact Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) _
      refine ⟨g, ?_, hgn, fun s hs => hmem s (AddSubgroup.subset_closure hs)⟩
      have hg0 : g ≠ 0 := by
        rw [hgdef]; exact (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
      have hg1 : g ≠ 1 := by
        intro hg
        apply htop
        rw [eq_top_iff]
        intro y _
        -- `h` is a unit multiple of `1`: Bézout gives `1 ∈ H`
        have hb := Nat.gcd_eq_gcd_ab (h : ZMod n).val n
        rw [← hgdef, hg] at hb
        have h1 : (1 : ZMod n) = ((Nat.gcdA (h : ZMod n).val n : ℤ) : ZMod n) * (h : ZMod n) := by
          have := congrArg (fun z : ℤ => (z : ZMod n)) hb
          push_cast at this
          rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val] at this
          rw [this, mul_comm]
        have h1H : (1 : ZMod n) ∈ H := by
          rw [h1, ← zsmul_eq_mul]
          exact H.zsmul_mem h.2 _
        have : y = (y.val : ℕ) • (1 : ZMod n) := by
          rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
        rw [this]
        exact H.nsmul_mem h1H _
      omega
    have := (circulant_no_consensus hS hn hg1 hgn hgS).1
    linarith
  · exact lam2_pos hn

/-! ### GCD graphs -/

/-- `D` is a set of proper divisors of `n`. -/
def ProperDivisors (n : ℕ) (D : Finset ℕ) : Prop := ∀ d ∈ D, d ∣ n ∧ d < n

theorem natCast_mem_gcdSet {D : Finset ℕ} (hD : ProperDivisors n D) {d : ℕ} (hd : d ∈ D) :
    (d : ZMod n) ∈ gcdSet n D := by
  unfold gcdSet
  rw [mem_filter, ZMod.val_natCast_of_lt (hD d hd).2, Nat.gcd_eq_left (hD d hd).1]
  exact ⟨mem_univ _, hd⟩

theorem dvd_val_of_mem_gcdSet {D : Finset ℕ} {s : ZMod n} (hs : s ∈ gcdSet n D) :
    D.gcd id ∣ s.val := by
  unfold gcdSet at hs
  rw [mem_filter] at hs
  exact (Finset.gcd_dvd hs.2).trans (Nat.gcd_dvd_left _ _)

/-- **Proposition 6.4 (i): connectivity of gcd graphs.**  For a set `D` of proper divisors of `n ≥ 2`, the gcd graph
`X_n(D)` is connected if and only if `gcd(D) = 1`. -/
theorem gcd_connected_iff (hn : 1 < n) {D : Finset ℕ} (hD : ProperDivisors n D) :
    AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) = ⊤ ↔ D.gcd id = 1 := by
  set H := AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) with hH
  constructor
  · intro htop
    by_contra hg
    set g := Nat.gcd (D.gcd id) n with hgdef
    have hgn : g ∣ n := Nat.gcd_dvd_right _ _
    have hg0 : g ≠ 0 := (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
    have hg1 : g ≠ 1 := by
      intro h1
      rcases D.eq_empty_or_nonempty with he | ⟨d, hd⟩
      · rw [he, Finset.gcd_empty] at hgdef
        rw [hgdef, Nat.gcd_zero_left] at h1
        omega
      · have : D.gcd id ∣ n := (Finset.gcd_dvd hd).trans (hD d hd).1
        rw [hgdef, Nat.gcd_eq_left this] at h1
        exact hg h1
    have hgS : ∀ s ∈ gcdSet n D, g ∣ s.val := fun s hs =>
      (Nat.gcd_dvd_left _ _).trans (dvd_val_of_mem_gcdSet hs)
    have hz := (circulant_no_consensus (gcdSet_symm D) hn (by omega) hgn hgS).1
    have hp := lam2_pos (S := gcdSet n D) hn htop
    linarith
  · intro h1
    -- every `gcd` of a subfamily of `D` lies in `H`
    have hsub : ∀ T : Finset ℕ, T ⊆ D → ((T.gcd id : ℕ) : ZMod n) ∈ H := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro _; rw [Finset.gcd_empty, Nat.cast_zero]; exact H.zero_mem
      | insert a T ha ih =>
        intro hT
        have haD : a ∈ D := hT (mem_insert_self a T)
        have hTH := ih ((subset_insert a T).trans hT)
        have haH : (a : ZMod n) ∈ H := AddSubgroup.subset_closure (natCast_mem_gcdSet hD haD)
        rw [Finset.gcd_insert, id]
        change ((Nat.gcd a (T.gcd id) : ℕ) : ZMod n) ∈ H
        have hb := Nat.gcd_eq_gcd_ab a (T.gcd id)
        have hc : ((Nat.gcd a (T.gcd id) : ℕ) : ZMod n)
            = (Nat.gcdA a (T.gcd id) : ZMod n) * (a : ZMod n)
              + (Nat.gcdB a (T.gcd id) : ZMod n) * ((T.gcd id : ℕ) : ZMod n) := by
          have := congrArg (fun z : ℤ => (z : ZMod n)) hb
          push_cast at this
          rw [this]; ring
        rw [hc, ← zsmul_eq_mul, ← zsmul_eq_mul]
        exact H.add_mem (H.zsmul_mem haH _) (H.zsmul_mem hTH _)
    have h1H : (1 : ZMod n) ∈ H := by
      have := hsub D subset_rfl
      rwa [h1, Nat.cast_one] at this
    rw [eq_top_iff]
    intro y _
    have : y = (y.val : ℕ) • (1 : ZMod n) := by
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rw [this]
    exact H.nsmul_mem h1H _

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
      ∀ t : ℕ, (ρ ^ 2) ^ t * sqNorm (err x) ≤ sqNorm (err ((cStep S ε)^[t] x)) := by
  intro S ne Cp Cm ρ
  have hS : IsSymm S := gcdSet_symm D
  have htop := (gcd_connected_iff hn hD).mpr hgcd
  obtain ⟨kp, hkp, hp⟩ := exists_mem_eq_sup' ne (cSym S)
  obtain ⟨km, hkm, hm⟩ := exists_mem_eq_inf' ne (cSym S)
  have hkp0 : kp ≠ 0 := ne_of_mem_erase hkp
  have hkm0 : km ≠ 0 := ne_of_mem_erase hkm
  have hCp : Cp = cSym S kp := hp
  have hCm : Cm = cSym S km := hm
  set a := (#S : ℝ) - Cp with ha
  set b := (#S : ℝ) - Cm with hb
  have hlo : ∀ k : ZMod n, k ≠ 0 → a ≤ (#S : ℝ) - cSym S k ∧ (#S : ℝ) - cSym S k ≤ b := by
    intro k hk
    have hmem : k ∈ univ.erase (0 : ZMod n) := mem_erase.mpr ⟨hk, mem_univ _⟩
    exact ⟨by have := le_sup' (cSym S) hmem; linarith,
      by have := inf'_le (cSym S) hmem; linarith⟩
  have hlam : lam2 S hn = a := by
    refine le_antisymm ?_ ?_
    · have := lam2_le S hn kp hkp0
      rw [ha, hCp]
      exact this
    · unfold lam2
      exact (le_inf'_iff _ _).mpr fun k hk => (hlo k (ne_of_mem_erase hk)).1
  have ha0 : 0 < a := hlam ▸ lam2_pos hn htop
  have hab' : a ≤ b := by
    have := (hlo kp hkp0).2
    rw [ha, hCp]
    exact this
  have hρ : ρ = (b - a) / (a + b) := by
    simp only [ρ, ha, hb]
    congr 1 <;> ring
  have hden : 2 * (#S : ℝ) - Cp - Cm = a + b := by rw [ha, hb]; ring
  obtain ⟨h0, h1, hconv⟩ := circulant_consensus hS ha0 hab' hlo
  refine ⟨hlam, ha0, hρ ▸ h0, hρ ▸ h1, fun x => ?_, fun ε => ?_⟩
  · rw [hden, hρ]
    exact hconv x
  · -- optimality: one of the two extreme modes decays no faster than `ρ`
    have hs : 0 < a + b := by linarith
    have hlb := rate_lower_bound (ε := ε) hs ha0.le hab' (ρ := ρ) (by rw [hρ]; field_simp)
    have hρ0 : 0 ≤ ρ := hρ ▸ h0
    have hpa : (#S : ℝ) - cSym S kp = a := by rw [ha, hCp]
    have hmb : (#S : ℝ) - cSym S km = b := by rw [hb, hCm]
    rcases le_total |1 - ε * a| |1 - ε * b| with hle | hle
    · rw [max_eq_right hle] at hlb
      obtain ⟨hne, hex⟩ := circulant_mode_exact hS hkm0 ε
      refine ⟨cosMode km, hne, fun t => ?_⟩
      rw [hex t, hmb]
      refine mul_le_mul_of_nonneg_right ?_ (sqNorm_nonneg _)
      refine pow_le_pow_left₀ (sq_nonneg _) ?_ t
      rw [← sq_abs (1 - ε * b)]
      exact pow_le_pow_left₀ hρ0 hlb 2
    · rw [max_eq_left hle] at hlb
      obtain ⟨hne, hex⟩ := circulant_mode_exact hS hkp0 ε
      refine ⟨cosMode kp, hne, fun t => ?_⟩
      rw [hex t, hpa]
      refine mul_le_mul_of_nonneg_right ?_ (sqNorm_nonneg _)
      refine pow_le_pow_left₀ (sq_nonneg _) ?_ t
      rw [← sq_abs (1 - ε * a)]
      exact pow_le_pow_left₀ hρ0 hlb 2

/-- **Proposition 6.4 (iii): the disconnected case.**  If `gcd(D) ≠ 1`, then `X_n(D)` is disconnected,
`λ₂ = 0`, and there is a non-constant initial vector that every constant-step iteration leaves
fixed, so global consensus does not occur from it. -/
theorem gcd_no_consensus (hn : 1 < n) {D : Finset ℕ} (hD : ProperDivisors n D)
    (hgcd : D.gcd id ≠ 1) :
    AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) ≠ ⊤ ∧
    lam2 (gcdSet n D) hn = 0 ∧
    ∃ x : ZMod n → ℝ, err x ≠ 0 ∧
      (∀ (ε : ℝ) (t : ℕ), (cStep (gcdSet n D) ε)^[t] x = x) ∧
      ∀ ε : ℝ, ¬ Tendsto (fun t : ℕ => sqNorm (err ((cStep (gcdSet n D) ε)^[t] x))) atTop (𝓝 0) := by
  have hnc : AddSubgroup.closure ((gcdSet n D : Finset (ZMod n)) : Set (ZMod n)) ≠ ⊤ :=
    fun h => hgcd ((gcd_connected_iff hn hD).mp h)
  set g := Nat.gcd (D.gcd id) n with hgdef
  have hgn : g ∣ n := Nat.gcd_dvd_right _ _
  have hg0 : g ≠ 0 := (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  have hg1 : g ≠ 1 := by
    intro h1
    rcases D.eq_empty_or_nonempty with he | ⟨d, hd⟩
    · rw [he, Finset.gcd_empty] at hgdef
      rw [hgdef, Nat.gcd_zero_left] at h1
      omega
    · have : D.gcd id ∣ n := (Finset.gcd_dvd hd).trans (hD d hd).1
      rw [hgdef, Nat.gcd_eq_left this] at h1
      exact hgcd h1
  have hgS : ∀ s ∈ gcdSet n D, g ∣ s.val := fun s hs =>
    (Nat.gcd_dvd_left _ _).trans (dvd_val_of_mem_gcdSet hs)
  obtain ⟨hz, hne, hfix⟩ := circulant_no_consensus (gcdSet_symm D) hn (by omega) hgn hgS
  refine ⟨hnc, hz, subIndicator n g, hne, hfix, fun ε hlim => ?_⟩
  have hconst : (fun t : ℕ => sqNorm (err ((cStep (gcdSet n D) ε)^[t] (subIndicator n g))))
      = fun _ => sqNorm (err (subIndicator n g)) := by
    funext t; rw [hfix ε t]
  rw [hconst, tendsto_const_nhds_iff] at hlim
  apply hne
  funext j
  have hzero := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (err (subIndicator n g) j))).mp
    hlim j (mem_univ _)
  simpa using hzero

/-- **Example 6.5.**  For `n = 6` and `D = {2}` the gcd graph is two disjoint triangles:
it is disconnected, `λ₂ = 0`, and consensus fails from a non-constant initial vector. -/
theorem gcd_example_six_two :
    AddSubgroup.closure ((gcdSet 6 {2} : Finset (ZMod 6)) : Set (ZMod 6)) ≠ ⊤ ∧
    lam2 (gcdSet 6 {2}) (by norm_num) = 0 ∧
    ∃ x : ZMod 6 → ℝ, err x ≠ 0 ∧ ∀ (ε : ℝ) (t : ℕ), (cStep (gcdSet 6 {2}) ε)^[t] x = x := by
  have hD : ProperDivisors 6 {2} := by
    intro d hd
    rw [mem_singleton] at hd
    subst hd
    norm_num
  have hg : ({2} : Finset ℕ).gcd id ≠ 1 := by simp
  obtain ⟨h1, h2, x, hx, hfix, _⟩ := gcd_no_consensus (by norm_num) hD hg
  exact ⟨h1, h2, x, hx, hfix⟩

end ArithmeticDynamics
