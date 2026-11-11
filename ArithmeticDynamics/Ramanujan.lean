/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part V: Ramanujan sums and Hölder's formula  `c_n(j) = φ(n) · μ(M)/φ(M)`,  `M = ord(j)`
(equation (2.3) of the paper), proved from scratch.
-/
import Mathlib
import ArithmeticDynamics.Extremal

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
