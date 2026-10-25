import Submission.Obl.k4_real_conic_restoration.Basic

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Submission.Obl.k4_real_conic_restoration

/-- The three mixed terms, with their common factor two omitted. -/
def mixed (S : Mat) (v : Vec) : ℝ :=
  S 0 1 * v 0 * v 1 + S 0 2 * v 0 * v 2 + S 1 2 * v 1 * v 2

theorem quad_decompose {S : Mat} (hS : S.IsSymm) (v : Vec) :
    quad S v = S 0 0 * v 0 ^ 2 + S 1 1 * v 1 ^ 2 + S 2 2 * v 2 ^ 2 + 2 * mixed S v := by
  simp only [quad, mixed, Fin.sum_univ_three, hS.apply 0 1, hS.apply 0 2, hS.apply 1 2]
  ring

theorem mixed_bound {S : Mat} {v : Vec} {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (hS : S.IsSymm) (hd : ∀ i, |S i i| ≤ ε) (hv : ∀ i, |v i| ≤ B)
    (hq : |quad S v| ≤ ε) : |mixed S v| ≤ 2 * ε * B ^ 2 := by
  have hB0 : 0 ≤ B := by linarith
  have hb2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have ht (i : Fin 3) : |S i i * v i ^ 2| ≤ ε * B ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul (hd i) (pow_le_pow_left₀ (abs_nonneg _) (hv i) 2)
      (by positivity) hε
  have h0 := abs_le.mp (ht 0)
  have h1 := abs_le.mp (ht 1)
  have h2 := abs_le.mp (ht 2)
  have hq' := abs_le.mp hq
  have he := quad_decompose hS v
  have hep : ε ≤ ε * B ^ 2 := le_mul_of_one_le_right hε hb2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Solve the last two mixed-term equations, with all divisions cleared. -/
theorem mixed_solve_bound {u v w B E : ℝ} {x y : Vec}
    (hB : 1 ≤ B) (hE : 0 ≤ E)
    (hx : ∀ i, |x i| ≤ B) (hy : ∀ i, |y i| ≤ B)
    (hx2 : 1 ≤ B * |x 2|) (hy2 : 1 ≤ B * |y 2|)
    (hm : 1 ≤ B * |x 0 * y 1 - y 0 * x 1|)
    (hf : |u * x 0 * x 1 + v * x 0 * x 2 + w * x 1 * x 2| ≤ E)
    (hg : |u * y 0 * y 1 + v * y 0 * y 2 + w * y 1 * y 2| ≤ E) :
    |v| ≤ 2 * E * B ^ 5 + 2 * |u| * B ^ 7 := by
  have hB0 : 0 ≤ B := by linarith
  let f := u * x 0 * x 1 + v * x 0 * x 2 + w * x 1 * x 2
  let g := u * y 0 * y 1 + v * y 0 * y 2 + w * y 1 * y 2
  let d := (x 0 * y 1 - y 0 * x 1) * x 2 * y 2
  have hid : v * d = f * y 1 * y 2 - g * x 1 * x 2 -
      u * x 1 * y 1 * (x 0 * y 2 - y 0 * x 2) := by dsimp [d, f, g]; ring
  have hab (i j : Fin 3) : |x i * y j| ≤ B ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hx i) (hy j) (abs_nonneg _) hB0
  have hxy : |x 0 * y 2 - y 0 * x 2| ≤ 2 * B ^ 2 := by
    calc
      _ ≤ |x 0 * y 2| + |y 0 * x 2| := abs_sub _ _
      _ ≤ _ := by have h := hab 2 0; rw [mul_comm (y 0)]
                  linarith [hab 0 2]
  have hft : |f * y 1 * y 2| ≤ E * B ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ E * B * B := by gcongr; exact hy 1; exact hy 2
      _ = _ := by ring
  have hgt : |g * x 1 * x 2| ≤ E * B ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ E * B * B := by gcongr; exact hx 1; exact hx 2
      _ = _ := by ring
  have hut : |u * x 1 * y 1 * (x 0 * y 2 - y 0 * x 2)| ≤ 2 * |u| * B ^ 4 := by
    simp only [abs_mul]
    calc
      _ ≤ |u| * B * B * (2 * B ^ 2) := by gcongr; exact hx 1; exact hy 1
      _ = _ := by ring
  have hnum : |v * d| ≤ 2 * E * B ^ 2 + 2 * |u| * B ^ 4 := by
    have h1 := abs_le.mp hft
    have h2 := abs_le.mp hgt
    have h3 := abs_le.mp hut
    rw [hid]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hden : 1 ≤ B ^ 3 * |d| := by
    have h := mul_le_mul hm hx2 (by positivity) (by linarith : 0 ≤ B * |x 0 * y 1 - y 0 * x 1|)
    have hh := mul_le_mul h hy2 (by positivity) (by linarith : 0 ≤ (B * |x 0 * y 1 - y 0 * x 1|) * (B * |x 2|))
    simpa only [one_mul, d, abs_mul] using hh.trans_eq (by ring)
  calc
    |v| ≤ |v| * (B ^ 3 * |d|) := le_mul_of_one_le_right (abs_nonneg _) hden
    _ = B ^ 3 * |v * d| := by rw [abs_mul v d]; ring
    _ ≤ B ^ 3 * (2 * E * B ^ 2 + 2 * |u| * B ^ 4) := by gcongr
    _ = _ := by ring

theorem coeff_decompose {S : Mat} (hS : S.IsSymm) :
    coeff S = |S 0 0| + |S 1 1| + |S 2 2| +
      2 * (|S 0 1| + |S 0 2| + |S 1 2|) := by
  simp only [coeff, Fin.sum_univ_three, hS.apply 0 1, hS.apply 0 2, hS.apply 1 2]
  ring

/-- Every mixed coefficient is quantitatively nonzero. -/
theorem offdiag_lower {S : Mat} {x y : Vec} {B ε : ℝ}
    (hB : 4 ≤ B) (hε : 0 ≤ ε) (hs : ε * B ^ 12 ≤ 1)
    (hS : S.IsSymm) (hd : ∀ i, |S i i| ≤ ε) (hc : 1 ≤ B * coeff S)
    (hx : ∀ i, |x i| ≤ B) (hy : ∀ i, |y i| ≤ B)
    (hxl : ∀ i, 1 ≤ B * |x i|) (hyl : ∀ i, 1 ≤ B * |y i|)
    (hm : ∀ i j, i ≠ j → 1 ≤ B * |x i * y j - y i * x j|)
    (hqx : |quad S x| ≤ ε) (hqy : |quad S y| ≤ ε) :
    1 ≤ B ^ 12 * |S 0 1| := by
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hv := mixed_solve_bound hB1 (by positivity : 0 ≤ 2 * ε * B ^ 2) hx hy
    (hxl 2) (hyl 2) (hm 0 1 (by decide))
    (mixed_bound hB1 hε hS hd hx hqx) (mixed_bound hB1 hε hS hd hy hqy)
  have hw := mixed_solve_bound (u := S 0 1) (v := S 1 2) (w := S 0 2)
    (x := ![x 1, x 0, x 2]) (y := ![y 1, y 0, y 2]) hB1
    (by positivity : 0 ≤ 2 * ε * B ^ 2)
    (by intro i; fin_cases i <;> simpa using hx _)
    (by intro i; fin_cases i <;> simpa using hy _)
    (by simpa using hxl 2) (by simpa using hyl 2)
    (by simpa using hm 1 0 (by decide))
    (by
      change |S 0 1 * x 1 * x 0 + S 1 2 * x 1 * x 2 + S 0 2 * x 0 * x 2| ≤ 2 * ε * B ^ 2
      rw [show S 0 1 * x 1 * x 0 + S 1 2 * x 1 * x 2 + S 0 2 * x 0 * x 2 = mixed S x by
        dsimp [mixed]; ring]
      exact mixed_bound hB1 hε hS hd hx hqx)
    (by
      change |S 0 1 * y 1 * y 0 + S 1 2 * y 1 * y 2 + S 0 2 * y 0 * y 2| ≤ 2 * ε * B ^ 2
      rw [show S 0 1 * y 1 * y 0 + S 1 2 * y 1 * y 2 + S 0 2 * y 0 * y 2 = mixed S y by
        dsimp [mixed]; ring]
      exact mixed_bound hB1 hε hS hd hy hqy)
  have hb7 : 1 ≤ B ^ 7 := one_le_pow₀ hB1
  have hep : ε ≤ ε * B ^ 7 := le_mul_of_one_le_right hε hb7
  have hup : |S 0 1| ≤ |S 0 1| * B ^ 7 := le_mul_of_one_le_right (abs_nonneg _) hb7
  have hc' : coeff S ≤ 30 * B ^ 7 * (ε + |S 0 1|) := by
    rw [coeff_decompose hS]
    have h0 := hd 0
    have h1 := hd 1
    have h2 := hd 2
    nlinarith [show 0 ≤ B ^ 7 * |S 0 1| by positivity]
  by_contra hn
  have hu : B ^ 12 * |S 0 1| < 1 := lt_of_not_ge hn
  have hh : B ^ 4 ≤ 30 * (ε * B ^ 12 + B ^ 12 * |S 0 1|) := by
    calc
      B ^ 4 ≤ B ^ 4 * (B * coeff S) := le_mul_of_one_le_right (by positivity) hc
      _ ≤ B ^ 4 * (B * (30 * B ^ 7 * (ε + |S 0 1|))) := by gcongr
      _ = _ := by ring
  have hp : (4 : ℝ) ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ (by norm_num) hB 4
  norm_num at hp
  linarith

theorem quad_reindex (S : Mat) (v : Vec) (σ : Equiv.Perm (Fin 3)) :
    quad (S.submatrix σ σ) (v ∘ σ) = quad S v := by
  unfold quad
  simp only [Matrix.submatrix_apply, Function.comp_apply]
  calc
    _ = ∑ a, ∑ b, v (σ a) * S (σ a) b * v b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp σ (fun b => v (σ a) * S (σ a) b * v b)
    _ = _ := Equiv.sum_comp σ (fun a => ∑ b, v a * S a b * v b)

theorem coeff_reindex (S : Mat) (σ : Equiv.Perm (Fin 3)) :
    coeff (S.submatrix σ σ) = coeff S := by
  unfold coeff
  simp only [Matrix.submatrix_apply]
  calc
    _ = ∑ a, ∑ b, |S (σ a) b| := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp σ (fun b => |S (σ a) b|)
    _ = _ := Equiv.sum_comp σ (fun a => ∑ b, |S a b|)

theorem small_power {B ε : ℝ} {m n : ℕ} (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (h : ε * B ^ n ≤ 1) (hmn : m ≤ n) : ε * B ^ m ≤ 1 :=
  (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hmn) hε).trans h

theorem normal_form_det_lower {S : Mat} {x y : Vec} {B ε : ℝ}
    (hB : 4 ≤ B) (hε : 0 ≤ ε) (hs : ε * B ^ 50 ≤ 1)
    (hS : S.IsSymm) (hd : ∀ i, |S i i| ≤ ε) (hc : 1 ≤ B * coeff S)
    (hSb : ∀ i j, |S i j| ≤ B)
    (hx : ∀ i, |x i| ≤ B) (hy : ∀ i, |y i| ≤ B)
    (hxl : ∀ i, 1 ≤ B * |x i|) (hyl : ∀ i, 1 ≤ B * |y i|)
    (hm : ∀ i j, i ≠ j → 1 ≤ B * |x i * y j - y i * x j|)
    (hqx : |quad S x| ≤ ε) (hqy : |quad S y| ≤ ε) :
    1 ≤ B ^ 36 * |S.det| := by
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hs12 := small_power hB1 hε hs (by decide : 12 ≤ 50)
  have hp (σ : Equiv.Perm (Fin 3)) : 1 ≤ B ^ 12 * |S (σ 0) (σ 1)| := by
    have hr := offdiag_lower (S := S.submatrix σ σ) (x := x ∘ σ) (y := y ∘ σ)
      hB hε hs12 (hS.submatrix σ) (fun i => hd (σ i))
      (by simpa only [coeff_reindex] using hc)
      (fun i => hx (σ i)) (fun i => hy (σ i))
      (fun i => hxl (σ i)) (fun i => hyl (σ i))
      (fun i j hij => hm (σ i) (σ j) (σ.injective.ne hij))
      (by simpa only [quad_reindex] using hqx) (by simpa only [quad_reindex] using hqy)
    exact hr
  have hu : 1 ≤ B ^ 12 * |S 0 1| := hp (Equiv.refl _)
  have hv : 1 ≤ B ^ 12 * |S 0 2| := by
    simpa [Equiv.swap_apply_def] using hp (Equiv.swap 1 2)
  have hw : 1 ≤ B ^ 12 * |S 1 2| := by
    simpa [Equiv.swap_apply_def, hS.apply 1 2] using hp (Equiv.swap 0 2)
  have huv := mul_le_mul hu hv (by positivity)
    (by positivity : 0 ≤ B ^ 12 * |S 0 1|)
  have huvw := mul_le_mul huv hw (by positivity)
    (by positivity : 0 ≤ (B ^ 12 * |S 0 1|) * (B ^ 12 * |S 0 2|))
  have hprod : 1 ≤ B ^ 36 * |S 0 1 * S 0 2 * S 1 2| := by
    simpa only [one_mul, abs_mul] using huvw.trans_eq (by ring)
  have ht (i j k l m : Fin 3) : |S i i * S j k * S l m| ≤ ε * B ^ 2 := by
    simp only [abs_mul]
    calc
      _ ≤ ε * B * B := by gcongr; exact hd i; exact hSb j k; exact hSb l m
      _ = _ := by ring
  have heq : S.det - 2 * (S 0 1 * S 0 2 * S 1 2) =
      S 0 0 * S 1 1 * S 2 2 - S 0 0 * S 1 2 * S 1 2 -
      S 1 1 * S 0 2 * S 0 2 - S 2 2 * S 0 1 * S 0 1 := by
    rw [Matrix.det_fin_three]
    simp only [hS.apply 0 1, hS.apply 0 2, hS.apply 1 2]
    ring
  have herr : |S.det - 2 * (S 0 1 * S 0 2 * S 1 2)| ≤ 4 * ε * B ^ 2 := by
    have h1 := abs_le.mp (ht 0 1 1 2 2)
    have h2 := abs_le.mp (ht 0 1 2 1 2)
    have h3 := abs_le.mp (ht 1 0 2 0 2)
    have h4 := abs_le.mp (ht 2 0 1 0 1)
    rw [heq]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htri : 2 * |S 0 1 * S 0 2 * S 1 2| ≤ |S.det| + 4 * ε * B ^ 2 := by
    calc
      _ = |2 * (S 0 1 * S 0 2 * S 1 2)| := by simp only [abs_mul]; norm_num
      _ = |S.det - (S.det - 2 * (S 0 1 * S 0 2 * S 1 2))| := by congr 1; ring
      _ ≤ |S.det| + |S.det - 2 * (S 0 1 * S 0 2 * S 1 2)| := abs_sub _ _
      _ ≤ _ := by gcongr
  have hB12 : 4 ≤ B ^ 12 := by
    calc
      4 ≤ B := hB
      _ = B ^ 1 := by simp
      _ ≤ B ^ 12 := pow_le_pow_right₀ hB1 (by decide)
  have hsmall : B ^ 36 * (4 * ε * B ^ 2) ≤ 1 := by
    calc
      _ = 4 * ε * B ^ 38 := by ring
      _ ≤ B ^ 12 * ε * B ^ 38 := by gcongr
      _ = ε * B ^ 50 := by ring
      _ ≤ 1 := hs
  have hmain := mul_le_mul_of_nonneg_left htri (show 0 ≤ B ^ 36 by positivity)
  nlinarith

end Submission.Obl.k4_real_conic_restoration
