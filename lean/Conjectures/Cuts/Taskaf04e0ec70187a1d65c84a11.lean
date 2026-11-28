import Mathlib
import Conjectures.Goldbach.RhSchoenfeldPsi

noncomputable section

namespace Conjectures.Cuts.Taskaf04e0ec70187a1d65c84a11_aux

open Real Chebyshev

private lemma log_le_sqrt_self {a : ℝ} (ha : 0 < a) : log a ≤ √a := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have h1 := Real.log_le_sub_one_of_pos (div_pos hs (Real.exp_pos 1))
  rw [Real.log_div hs.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_sqrt ha.le] at h1
  have he := Real.exp_one_gt_d9
  have h2 : 2 * √a / exp 1 ≤ √a := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith
  rw [mul_div_assoc] at h2
  linarith

private lemma prime_power_gap {x : ℝ} (hx : (10 : ℝ) ^ (10 : ℕ) ≤ x) :
    ψ x - θ x ≤ 1.9 * √x := by
  have hx0 : 0 < x := by linarith
  let a : ℝ := x ^ ((1 : ℝ) / 6)
  have ha : 0 < a := Real.rpow_pos_of_pos hx0 _
  have hx6 : a ^ 6 = x := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hs : √x = a ^ 3 := by
    rw [← hx6, show a ^ 6 = (a ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h2 : x ^ (2 : ℝ)⁻¹ = a ^ 3 := by rwa [Real.sqrt_eq_rpow, one_div] at hs
  have h3 : x ^ (3 : ℝ)⁻¹ = a ^ 2 := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have h40 : 40 ≤ a := by
    by_contra! ht
    have hpow := pow_lt_pow_left₀ ht ha.le (by norm_num : 6 ≠ 0)
    norm_num at hpow
    linarith
  have hl4 : log 4 ≤ 1.4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    linarith [Real.log_two_lt_d9]
  have hcomp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h5 : ψ (x ^ (5 : ℝ)⁻¹) ≤ ψ (x ^ (3 : ℝ)⁻¹) :=
    Chebyshev.psi_mono (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  rw [h2, h3] at hcomp
  rw [h3] at h5
  have hl3 : log (a ^ 3) ≤ 3 * √a := by
    rw [Real.log_pow]
    norm_num
    linarith [log_le_sqrt_self ha]
  have hsq : √(a ^ 3) * √a = a ^ 2 := by
    rw [← Real.sqrt_mul (by positivity), show a ^ 3 * a = (a ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hsm : ψ (a ^ 2) ≤ 5.4 * a ^ 2 := by
    have hconst := Chebyshev.psi_le_const_mul_self (sq_nonneg a)
    exact hconst.trans (by gcongr; linarith)
  have hbig : ψ (a ^ 3) ≤ 1.4 * a ^ 3 + 6 * a ^ 2 := by
    have hone : 1 ≤ a ^ 3 := one_le_pow₀ (by linarith)
    have hpsi := Chebyshev.psi_le hone
    calc ψ (a ^ 3) ≤ log 4 * a ^ 3 + 2 * √(a ^ 3) * log (a ^ 3) := hpsi
      _ ≤ 1.4 * a ^ 3 + 2 * √(a ^ 3) * (3 * √a) := by gcongr
      _ = 1.4 * a ^ 3 + 6 * a ^ 2 := by linear_combination 6 * hsq
  have hdom : 40 * a ^ 2 ≤ a ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_right h40 (sq_nonneg a)
    linarith [show a * a ^ 2 = a ^ 3 by ring]
  rw [hs]
  linarith [hcomp, h5, hsm, hbig, hdom, sq_nonneg a]

private lemma scaled_log_lower : 2.21 ≤ log (3 * Real.pi) := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 9.3 / 8 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num),
    show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h
  norm_num at h
  have hpi := Real.pi_gt_d4
  have hh := Real.log_le_log (show (0 : ℝ) < 9.3 by norm_num) (show (9.3 : ℝ) ≤ 3 * Real.pi by linarith)
  linarith [Real.log_two_gt_d9]

private lemma log_above_bound {y : ℝ} (hy : 100000 ≤ y) : 11.4 ≤ log y := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 100000 / (2 ^ 16) by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow] at h
  norm_num at h
  have hlo := Real.log_le_log (show (0 : ℝ) < 100000 by norm_num) hy
  linarith [Real.log_two_gt_d9]

private lemma smoothing_scalar {y B : ℝ} (hy : 100000 ≤ y) (hB : 50 ≤ B) (hB' : B ≤ y / 3)
    (hlog : log (B / Real.pi) ≤ √(B / Real.pi)) :
    let Z := (log (B / Real.pi)) ^ 2 / (2 * Real.pi) + 9 / 20
    3.001 * y + (y + 3) * Z + 4 + 1.9 * y ≤ y * ((2 * log y) ^ 2 - 2 * (2 * log y)) / (8 * Real.pi) := by
  intro Z
  have hpi := Real.pi_pos
  have hpiL := Real.pi_gt_d4
  have hpiU := Real.pi_lt_d4
  have hy0 : 0 ≤ y := by linarith
  have hBp : 0 < B / Real.pi := div_pos (by linarith) hpi
  have hlogB : 0 ≤ log (B / Real.pi) := Real.log_nonneg ((le_div_iff₀ hpi).2 (by linarith))
  have hlog2 := pow_le_pow_left₀ hlogB hlog 2
  rw [Real.sq_sqrt hBp.le] at hlog2
  have hzSmall : 3 * Z + 4 ≤ 0.06 * y := by
    have hz1 : Z ≤ B / (2 * Real.pi ^ 2) + 9 / 20 := by
      change (log (B / Real.pi)) ^ 2 / (2 * Real.pi) + 9 / 20 ≤ B / (2 * Real.pi ^ 2) + 9 / 20
      have hdiv : (log (B / Real.pi)) ^ 2 / (2 * Real.pi) ≤ B / (2 * Real.pi ^ 2) := by
        calc (log (B / Real.pi)) ^ 2 / (2 * Real.pi)
            ≤ (B / Real.pi) / (2 * Real.pi) := div_le_div_of_nonneg_right hlog2 (by positivity)
          _ = B / (2 * Real.pi ^ 2) := by ring
      linarith
    have hd : (18 : ℝ) ≤ 2 * Real.pi ^ 2 := by nlinarith
    have hz2 : B / (2 * Real.pi ^ 2) ≤ (y / 3) / 18 :=
      (div_le_div_of_nonneg_left (by linarith) (by norm_num) hd).trans
        (div_le_div_of_nonneg_right hB' (by norm_num))
    linarith [hz1, hz2, hy]
  have hlogY := log_above_bound hy
  have hlogBY : log (B / Real.pi) ≤ log y - 2.21 := by
    have hbcomp : B / Real.pi ≤ y / (3 * Real.pi) := by
      rw [div_le_div_iff₀ hpi (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hB' hpi.le]
    have hh := Real.log_le_log hBp hbcomp
    rw [Real.log_div (by linarith) hpi.ne', Real.log_div (by linarith) (by positivity)] at hh
    rw [Real.log_div (by linarith) hpi.ne']
    linarith [scaled_log_lower]
  have hzMain := pow_le_pow_left₀ hlogB hlogBY 2
  have hz : Z ≤ (log y - 2.21) ^ 2 / (2 * Real.pi) + 9 / 20 := by
    change (log (B / Real.pi)) ^ 2 / (2 * Real.pi) + 9 / 20 ≤ _
    have hsub := div_le_div_of_nonneg_right hzMain (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
    linarith
  have hcoef : 3.001 + ((log y - 2.21) ^ 2 / (2 * Real.pi) + 9 / 20) + 0.06 + 1.9 ≤
      ((2 * log y) ^ 2 - 2 * (2 * log y)) / (8 * Real.pi) := by
    rw [le_div_iff₀ (show 0 < 8 * Real.pi by positivity)]
    have hmul : (3.001 + ((log y - 2.21) ^ 2 / (2 * Real.pi) + 9 / 20) + 0.06 + 1.9) * (8 * Real.pi) =
        4 * (log y - 2.21) ^ 2 + (3.001 + 9 / 20 + 0.06 + 1.9) * (8 * Real.pi) := by
      field_simp
      ring
    rw [hmul]
    nlinarith [hpiU, hlogY]
  calc 3.001 * y + (y + 3) * Z + 4 + 1.9 * y
      = y * (3.001 + Z + 1.9) + (3 * Z + 4) := by ring
    _ ≤ y * (3.001 + ((log y - 2.21) ^ 2 / (2 * Real.pi) + 9 / 20) + 1.9) + 0.06 * y := by gcongr
    _ = y * (3.001 + ((log y - 2.21) ^ 2 / (2 * Real.pi) + 9 / 20) + 0.06 + 1.9) := by ring
    _ ≤ y * (((2 * log y) ^ 2 - 2 * (2 * log y)) / (8 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hcoef hy0
    _ = y * ((2 * log y) ^ 2 - 2 * (2 * log y)) / (8 * Real.pi) := by ring

private theorem smooth_with_third (hRH : RiemannHypothesis) {x : ℝ} (hx : (10 : ℝ) ^ (10 : ℕ) ≤ x) :
    let y := √x
    let B : ℝ := ⌊y / 3⌋₊
    let Z := (log (B / Real.pi)) ^ 2 / (2 * Real.pi) + 9 / 20
    |ψ x - x| ≤ 3.001 * y + (y + 3) * Z + 4 := by
  intro y B Z
  have hx0 : 0 ≤ x := by linarith
  have hy : 100000 ≤ y := Real.le_sqrt_of_sq_le (by linarith)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg x
  have hy2 : y ^ 2 = x := Real.sq_sqrt hx0
  have hb1 : B ≤ y / 3 := Nat.floor_le (by linarith)
  have hb2 : y / 3 < B + 1 := Nat.lt_floor_add_one (y / 3)
  have hb : 50 ≤ B := by linarith
  have hB : 0 < B := by linarith
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let n : ℕ := ⌊x⌋₊
  have hn1 : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hn2 : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hn : 2 ≤ n := Nat.le_floor (by norm_num; linarith)
  have hsn : √(n : ℝ) ≤ y := Real.sqrt_le_sqrt hn1
  have hN (d : ℝ) (hd : B - 1 / 2 ≤ d) : (n : ℝ) / d ≤ 3.001 * y := by
    rw [div_le_iff₀ (by linarith : 0 < d)]
    have e : y / 3 - 1.5 ≤ d := by linarith
    have hmul := mul_le_mul_of_nonneg_left e hy0
    have h1 : 13504.5 ≤ y := by linarith
    nlinarith [mul_nonneg hy0 (sub_nonneg.2 h1)]
  let W := SchoenfeldRH.zeroSumW B
  have hw : 0 ≤ W := SchoenfeldRH.zeroSumW_nonneg B
  have hBW : B * W ≤ Z := SchoenfeldRH.zeroSumW_le_of_RH' hRH B hb
  have hU := SchoenfeldRH.psi_sub_le_of_RH hRH n hn (B + 1 / 2) (by linarith)
  have hne (k : ℕ) : B - 1 / 2 ≠ 2 * (k : ℝ) := by
    intro h
    have he : (2 : ℝ) * (⌊y / 3⌋₊ : ℝ) = 4 * (k : ℝ) + 1 := by change (2 : ℝ) * B = _; linarith
    have hnat : 2 * ⌊y / 3⌋₊ = 4 * k + 1 := by exact_mod_cast he
    omega
  have hL := SchoenfeldRH.sub_psi_le_of_RH hRH n hn (B - 1 / 2) (by linarith) hne
  rw [show B + 1 / 2 - 1 / 2 = B by ring] at hU
  rw [show B - 1 / 2 + 1 / 2 = B by ring] at hL
  have hupper : √(n : ℝ) * ((B + 1 / 2) * W) ≤ (y + 3) * Z := by
    calc √(n : ℝ) * ((B + 1 / 2) * W)
        ≤ y * ((B + 1 / 2) * W) := by gcongr
      _ = (y * (B + 1 / 2)) * W := by ring
      _ ≤ ((y + 3) * B) * W := mul_le_mul_of_nonneg_right (by nlinarith) hw
      _ = (y + 3) * (B * W) := by ring
      _ ≤ (y + 3) * Z := by gcongr
  have hprod : 0 ≤ (B - 1 / 2) * W := mul_nonneg (by linarith) hw
  have hlower : (√(n : ℝ) + 1) * ((B - 1 / 2) * W) ≤ (y + 3) * Z := by
    calc (√(n : ℝ) + 1) * ((B - 1 / 2) * W)
        ≤ (y + 3) * (B * W) := by gcongr <;> linarith
      _ ≤ (y + 3) * Z := by gcongr
  rw [Chebyshev.psi_eq_psi_coe_floor, abs_le]
  constructor <;> linarith [hN (B + 1 / 2 - 1) (by linarith), hN (B - 1 / 2 + 1) (by linarith)]

private theorem high_theta_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : (10 : ℝ) ^ (10 : ℕ) ≤ x) :
    |θ x - x| ≤ √x * (log x ^ 2 - 2 * log x) / (8 * Real.pi) := by
  let y := √x
  let B : ℝ := ⌊y / 3⌋₊
  let Z := (log (B / Real.pi)) ^ 2 / (2 * Real.pi) + 9 / 20
  have hy : 100000 ≤ y := Real.le_sqrt_of_sq_le (by linarith)
  have hb' : y / 3 < B + 1 := Nat.lt_floor_add_one (y / 3)
  have hb1 : 50 ≤ B := by linarith
  have hb2 : B ≤ y / 3 := Nat.floor_le (by linarith)
  have hsm : |ψ x - x| ≤ 3.001 * y + (y + 3) * Z + 4 := smooth_with_third hRH hx
  have hg := prime_power_gap hx
  have hval := smoothing_scalar hy hb1 hb2 (log_le_sqrt_self (div_pos (by linarith) Real.pi_pos))
  have hlog : 2 * log y = log x := by
    dsimp [y]
    rw [Real.log_sqrt (by linarith)]
    ring
  change 3.001 * y + (y + 3) * Z + 4 + 1.9 * y ≤ y * ((2 * log y) ^ 2 - 2 * (2 * log y)) / (8 * Real.pi) at hval
  rw [hlog] at hval
  have he : θ x - x = (ψ x - x) - (ψ x - θ x) := by ring
  rw [he]
  have htri := abs_sub (ψ x - x) (ψ x - θ x)
  rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))] at htri
  exact htri.trans (by linarith [hsm, hg, hval])

private theorem rh_of_halfPlane
    (h : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
  intro s hzero htriv hs1
  by_contra hre
  rcases lt_or_gt_of_ne hre with hlt | hgt
  swap
  · exact h s hgt hs1 hzero
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hzero
    norm_num at hzero
  have hw : 1 / 2 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hw1 : 1 - s ≠ 1 := fun h0 => hs0 (by linear_combination -h0)
  have hwn : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n h0
    have hre0 := congrArg Complex.re h0
    rw [Complex.neg_re, Complex.natCast_re] at hre0
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub hwn hw1
  rw [sub_sub_cancel, hzero] at hfe
  have hζ : riemannZeta (1 - s) ≠ 0 := h _ hw hw1
  have hΓ : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hwn
  have hpow : (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h0 => mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) h0.1
  have hcos : Complex.cos (Real.pi * (1 - s) / 2) = 0 := by
    by_contra hc
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hc) hζ hfe.symm
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 hcos
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hsk : s = -2 * (k : ℂ) := by
    have h3 : (Real.pi : ℂ) * (s + 2 * k) = 0 := by linear_combination -2 * hk
    have h4 := (mul_eq_zero.1 h3).resolve_left hπ
    linear_combination h4
  have hk1 : 1 ≤ k := by
    by_contra hk1
    have hk0 : k ≤ 0 := by omega
    rcases eq_or_lt_of_le hk0 with hk0 | hk0
    · exact hs0 (by simp [hsk, hk0])
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      have hsre : s.re = -2 * (k : ℝ) := by simp [hsk]
      linarith
  refine htriv ⟨(k - 1).toNat, ?_⟩
  have hcast : (((k - 1).toNat : ℤ) : ℂ) = ((k - 1 : ℤ) : ℂ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  rw [Int.cast_natCast] at hcast
  rw [hcast, hsk]
  push_cast
  ring

end Conjectures.Cuts.Taskaf04e0ec70187a1d65c84a11_aux

theorem Conjectures.Cuts.Taskaf04e0ec70187a1d65c84a11 : ((∀ (x1 : ℕ) [x2 : NeZero x1] (x3 : DirichletCharacter ℂ x1) (x4 : ℂ), (1 / 2 : ℝ) < x4.re → x3 ≠ (1 : DirichletCharacter ℂ x1) ∨ x4 ≠ (1 : ℂ) → DirichletCharacter.LFunction x3 x4 ≠ (0 : ℂ)) → ∀ (x2 : ℝ), (10 : ℝ) ^ (10 : ℕ) ≤ x2 → |Chebyshev.theta x2 - x2| ≤ √x2 * (Real.log x2 ^ (2 : ℕ) - (2 : ℝ) * Real.log x2) / ((8 : ℝ) * Real.pi)) := by
  intro hgrh x hx
  have hRH := Conjectures.Cuts.Taskaf04e0ec70187a1d65c84a11_aux.rh_of_halfPlane (fun s hs hne => by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using hgrh 1 1 s hs (Or.inr hne))
  exact Conjectures.Cuts.Taskaf04e0ec70187a1d65c84a11_aux.high_theta_of_RH hRH hx
