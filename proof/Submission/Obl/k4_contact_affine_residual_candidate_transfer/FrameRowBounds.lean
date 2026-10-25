import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameRows

/-!
# Bounded row constants of the residual labels

A trajectory of a retained node at a time of its block also lies in the
parent label at that time. Comparing the two original first rows there, and
using both horizontal centerings and the parent's second row, bounds every
row constant of the residual label by `20 * K ^ 2 * K₂`.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Frame

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

/-- The first row of the parent label is the chart center. -/
theorem FrameGood.parent_row_center (hg : FrameGood f Rk θ K₂ e₀') (l : α)
    (hl : l ∈ D.A k (f.depth 0) f.i₀) (t : ℝ) (ht : t ∈ f.block 0 f.i₀) :
    |D.x k l t 1 - f.Z₀| ≤ 2 * D.K k * f.q₀ := by
  obtain ⟨r1, -, -⟩ := hg.rows 0 (Nat.zero_le _) f.i₀ l hl t ht
  have hq := f.q₀_eq
  have hblk := f.block_eq_Icc 0 f.i₀
  rw [hblk] at ht
  have hc1 := hg.cbound 0 (Nat.zero_le _) f.i₀ 1
  have htt : |t - f.t₀| ≤ f.q₀ := by
    rw [abs_le]; rw [hq]; simp only [t₀] at *; constructor <;> linarith [ht.1, ht.2]
  have e : D.x k l t 1 - f.Z₀ = (D.x k l t 1 - D.c k (f.depth 0) f.i₀ 0 -
      t * D.c k (f.depth 0) f.i₀ 1) + (t - f.t₀) * D.c k (f.depth 0) f.i₀ 1 := by
    simp only [Z₀]; ring
  rw [e]
  calc
    _ ≤ |D.x k l t 1 - D.c k (f.depth 0) f.i₀ 0 - t * D.c k (f.depth 0) f.i₀ 1| +
        |t - f.t₀| * |D.c k (f.depth 0) f.i₀ 1| := by
      rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ D.K k * f.ql 0 + f.q₀ * D.K k :=
      add_le_add r1 (mul_le_mul htt hc1 (abs_nonneg _) f.q₀_pos.le)
    _ = 2 * D.K k * f.q₀ := by rw [← hq]; ring

/-- The row constants of a residual label are bounded. -/
theorem FrameGood.res_cbound (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) (e : Fin 5) :
    |(f.level h).c i e| ≤ 20 * D.K k ^ 2 * K₂ := by
  have hq := f.q₀_pos
  have hK : 1 ≤ D.K k := hg.K_ge
  have hK₂ : 1 ≤ K₂ := hg.K₂_ge
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  set oi := (f.node h i).1
  set c := D.c k (f.depth h) oi
  set c₀ := D.c k (f.depth 0) f.i₀
  obtain ⟨p, hpev, -⟩ := f.node_retained h i
  set l := p.1
  set t := p.2
  have hl : l ∈ f.hist h oi (f.node h i).2 := hpev.1
  have ht : t ∈ f.block h oi := hpev.2
  obtain ⟨hsub, hhist⟩ := hg.inside hh i
  have hlA : l ∈ D.A k (f.depth h) oi := f.hist_subset_A h oi _ hl
  have hlA₀ : l ∈ D.A k (f.depth 0) f.i₀ := f.hist_subset_A 0 f.i₀ f.u₀ (hhist hl)
  have ht₀ : t ∈ f.block 0 f.i₀ := hsub ht
  have hT := hg.T₀_le hh
  have hqq : f.ql h ≤ f.q₀ := by
    rw [f.q₀_eq]; simp only [ql]
    exact zpow_le_zpow_right₀ (by norm_num) (by simpa [T₀] using hT)
  have hql := f.ql_pos h
  -- positions inside the parent block
  have hblk₀ := f.block_eq_Icc 0 f.i₀
  have hq₀eq := f.q₀_eq
  have htt : |t - f.t₀| ≤ f.q₀ := by
    rw [hblk₀] at ht₀; rw [abs_le, hq₀eq]; simp only [t₀]
    constructor <;> linarith [ht₀.1, ht₀.2]
  have hmidblk : f.mid h oi ∈ f.block h oi := by
    rw [f.block_eq_Icc]; simp only [mid, left, ql, zpow_neg, zpow_natCast]
    constructor <;> field_simp <;> nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (f.Tl h)]
  have hmt : |f.mid h oi - f.t₀| ≤ f.q₀ := by
    have hm₀ := hsub hmidblk
    rw [hblk₀] at hm₀; rw [abs_le, hq₀eq]; simp only [t₀]
    constructor <;> linarith [hm₀.1, hm₀.2]
  have hmid₀blk : f.mid 0 f.i₀ ∈ f.block 0 f.i₀ := by
    rw [hblk₀]; simp only [mid, left, ql, zpow_neg, zpow_natCast]
    constructor <;> field_simp <;> nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (f.Tl 0)]
  have hmt₀ : |f.mid 0 f.i₀ - f.t₀| ≤ f.q₀ := by
    have hm₀ := hmid₀blk
    rw [hblk₀] at hm₀; rw [abs_le, hq₀eq]; simp only [t₀]
    constructor <;> linarith [hm₀.1, hm₀.2]
  -- original rows at the witness
  obtain ⟨r1, r2, -⟩ := hg.rows h hh oi l hlA t ht
  obtain ⟨-, r2₀, -⟩ := hg.rows 0 (Nat.zero_le _) f.i₀ l hlA₀ t ht₀
  have hZ := hg.parent_row_center l hlA₀ t ht₀
  have hcen := hg.centered h hh oi
  have hcen₀ := hg.centered 0 (Nat.zero_le _) f.i₀
  have hcb (e : Fin 5) : |c e| ≤ D.K k := hg.cbound h hh oi e
  have hcb₀ (e : Fin 5) : |c₀ e| ≤ D.K k := hg.cbound 0 (Nat.zero_le _) f.i₀ e
  -- transverse widths
  have hg₀ : D.N k ^ (-D.ℓ * f.depth 0) ≤ D.K k * f.q₀ := by
    rw [hg.ℓ_eq, hg.depth_zero]
    have := hg.width_over_q₀
    rwa [div_le_iff₀ hq] at this
  have hgg : D.N k ^ (-D.ℓ * f.depth h) ≤ D.N k ^ (-D.ℓ * f.depth 0) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [hg.N_ge])
    rw [hg.ℓ_eq, hg.depth_eq hh, hg.depth_eq (Nat.zero_le _)]
    have : 0 ≤ (h : ℝ) * (U' / f.m) := by
      have := hg.U'_pos; positivity
    have h00 : ((0 : ℕ) : ℝ) * (U' / f.m) = 0 := by simp
    rw [h00]
    nlinarith [hg.κ_pos]
  have hgE : D.K k * f.ql h * D.N k ^ (-D.ℓ * f.depth h) ≤ D.K k ^ 2 * f.q₀ ^ 2 := by
    calc
      D.K k * f.ql h * D.N k ^ (-D.ℓ * f.depth h) ≤ D.K k * f.q₀ * (D.K k * f.q₀) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hqq (by linarith)) (hgg.trans hg₀)
          (by positivity) (by positivity)
      _ = D.K k ^ 2 * f.q₀ ^ 2 := by ring
  have hgE₀ : D.K k * f.ql 0 * D.N k ^ (-D.ℓ * f.depth 0) ≤ D.K k ^ 2 * f.q₀ ^ 2 := by
    calc
      D.K k * f.ql 0 * D.N k ^ (-D.ℓ * f.depth 0) ≤ D.K k * f.q₀ * (D.K k * f.q₀) := by
        rw [← hq₀eq]; exact mul_le_mul_of_nonneg_left hg₀ (by positivity)
      _ = D.K k ^ 2 * f.q₀ ^ 2 := by ring
  -- abbreviations for the witness
  set Z := D.x k l t 1
  set Y := D.x k l t 2
  have hcen1 : |c 3 + c 0 + f.mid h oi * c 1| ≤ K₂ * f.q₀ :=
    (le_of_add_le_of_nonneg_left hcen (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hqq (by linarith))
  have hcen2 : |c 4 - f.mid h oi| ≤ K₂ * f.q₀ :=
    (le_of_add_le_of_nonneg_right hcen (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hqq (by linarith))
  have hcen1₀ : |c₀ 3 + c₀ 0 + f.mid 0 f.i₀ * c₀ 1| ≤ K₂ * f.q₀ := by
    rw [hq₀eq]; exact le_of_add_le_of_nonneg_left hcen₀ (abs_nonneg _)
  have hcen2₀ : |c₀ 4 - f.mid 0 f.i₀| ≤ K₂ * f.q₀ := by
    rw [hq₀eq]; exact le_of_add_le_of_nonneg_right hcen₀ (abs_nonneg _)
  -- the five residual constants, times the right powers of `q₀`
  have b0 : |c 0 + f.t₀ * c 1 - f.Z₀| ≤ 4 * D.K k * f.q₀ := by
    have e : c 0 + f.t₀ * c 1 - f.Z₀ = -(Z - c 0 - t * c 1) + (Z - f.Z₀) - (t - f.t₀) * c 1 := by
      ring
    rw [e]
    have h1 : |(t - f.t₀) * c 1| ≤ f.q₀ * D.K k := by
      rw [abs_mul]; exact mul_le_mul htt (hcb 1) (abs_nonneg _) hq.le
    have h2 : |Z - c 0 - t * c 1| ≤ D.K k * f.q₀ :=
      r1.trans (mul_le_mul_of_nonneg_left hqq (by linarith))
    calc
      _ ≤ |-(Z - c 0 - t * c 1)| + |Z - f.Z₀| + |(t - f.t₀) * c 1| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ D.K k * f.q₀ + 2 * D.K k * f.q₀ + f.q₀ * D.K k := by
        rw [abs_neg]; exact add_le_add (add_le_add h2 hZ) h1
      _ = 4 * D.K k * f.q₀ := by ring
  have b3 : |c 3 + f.Z₀| ≤ (K₂ + 5 * D.K k) * f.q₀ := by
    have e : c 3 + f.Z₀ = (c 3 + c 0 + f.mid h oi * c 1) - (c 0 + f.t₀ * c 1 - f.Z₀) -
        (f.mid h oi - f.t₀) * c 1 := by ring
    rw [e]
    have h1 : |(f.mid h oi - f.t₀) * c 1| ≤ f.q₀ * D.K k := by
      rw [abs_mul]; exact mul_le_mul hmt (hcb 1) (abs_nonneg _) hq.le
    calc
      _ ≤ |c 3 + c 0 + f.mid h oi * c 1| + |c 0 + f.t₀ * c 1 - f.Z₀| +
          |(f.mid h oi - f.t₀) * c 1| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ K₂ * f.q₀ + 4 * D.K k * f.q₀ + f.q₀ * D.K k := add_le_add (add_le_add hcen1 b0) h1
      _ = (K₂ + 5 * D.K k) * f.q₀ := by ring
  have b4 : |c 4 - f.t₀| ≤ (K₂ + 1) * f.q₀ := by
    calc
      _ = |(c 4 - f.mid h oi) + (f.mid h oi - f.t₀)| := by ring_nf
      _ ≤ |c 4 - f.mid h oi| + |f.mid h oi - f.t₀| := abs_add_le _ _
      _ ≤ K₂ * f.q₀ + f.q₀ := add_le_add hcen2 hmt
      _ = (K₂ + 1) * f.q₀ := by ring
  have b3₀ : |c₀ 3 + f.Z₀| ≤ (K₂ + D.K k) * f.q₀ := by
    have e : c₀ 3 + f.Z₀ = (c₀ 3 + c₀ 0 + f.mid 0 f.i₀ * c₀ 1) -
        (f.mid 0 f.i₀ - f.t₀) * c₀ 1 := by simp only [Z₀]; ring
    rw [e]
    have h1 : |(f.mid 0 f.i₀ - f.t₀) * c₀ 1| ≤ f.q₀ * D.K k := by
      rw [abs_mul]; exact mul_le_mul hmt₀ (hcb₀ 1) (abs_nonneg _) hq.le
    calc
      _ ≤ |c₀ 3 + c₀ 0 + f.mid 0 f.i₀ * c₀ 1| + |(f.mid 0 f.i₀ - f.t₀) * c₀ 1| :=
        abs_sub _ _
      _ ≤ K₂ * f.q₀ + f.q₀ * D.K k := add_le_add hcen1₀ h1
      _ = (K₂ + D.K k) * f.q₀ := by ring
  have b4₀ : |c₀ 4 - f.t₀| ≤ (K₂ + 1) * f.q₀ := by
    calc
      _ = |(c₀ 4 - f.mid 0 f.i₀) + (f.mid 0 f.i₀ - f.t₀)| := by ring_nf
      _ ≤ |c₀ 4 - f.mid 0 f.i₀| + |f.mid 0 f.i₀ - f.t₀| := abs_add_le _ _
      _ ≤ K₂ * f.q₀ + f.q₀ := add_le_add hcen2₀ hmt₀
      _ = (K₂ + 1) * f.q₀ := by ring
  have b2 : |c 2 + f.t₀ * c 3 + c 4 * f.Z₀ - f.Y₀| ≤ 18 * D.K k ^ 2 * K₂ * f.q₀ ^ 2 := by
    have e : c 2 + f.t₀ * c 3 + c 4 * f.Z₀ - f.Y₀ =
        (t - f.t₀) * ((c₀ 3 + f.Z₀) - (c 3 + f.Z₀)) +
          ((c₀ 4 - f.t₀) - (c 4 - f.t₀)) * (Z - f.Z₀) -
          (Y - c 2 - t * c 3 - c 4 * Z) + (Y - c₀ 2 - t * c₀ 3 - c₀ 4 * Z) := by
      simp only [Y₀]; ring
    rw [e]
    have hA : |(t - f.t₀) * ((c₀ 3 + f.Z₀) - (c 3 + f.Z₀))| ≤
        f.q₀ * ((K₂ + D.K k) * f.q₀ + (K₂ + 5 * D.K k) * f.q₀) := by
      rw [abs_mul]
      exact mul_le_mul htt ((abs_sub _ _).trans (add_le_add b3₀ b3)) (abs_nonneg _) hq.le
    have hB : |((c₀ 4 - f.t₀) - (c 4 - f.t₀)) * (Z - f.Z₀)| ≤
        ((K₂ + 1) * f.q₀ + (K₂ + 1) * f.q₀) * (2 * D.K k * f.q₀) := by
      rw [abs_mul]
      exact mul_le_mul ((abs_sub _ _).trans (add_le_add b4₀ b4)) hZ (abs_nonneg _)
        (by positivity)
    have hC : |Y - c 2 - t * c 3 - c 4 * Z| ≤ D.K k ^ 2 * f.q₀ ^ 2 := r2.trans hgE
    have hD : |Y - c₀ 2 - t * c₀ 3 - c₀ 4 * Z| ≤ D.K k ^ 2 * f.q₀ ^ 2 := r2₀.trans hgE₀
    set A := (t - f.t₀) * ((c₀ 3 + f.Z₀) - (c 3 + f.Z₀))
    set B := ((c₀ 4 - f.t₀) - (c 4 - f.t₀)) * (Z - f.Z₀)
    set C := Y - c 2 - t * c 3 - c 4 * Z
    set E := Y - c₀ 2 - t * c₀ 3 - c₀ 4 * Z
    have tri : |A + B - C + E| ≤ |A| + |B| + |C| + |E| := by
      calc
        |A + B - C + E| ≤ |A + B - C| + |E| := abs_add_le _ _
        _ ≤ (|A + B| + |C|) + |E| := add_le_add (abs_sub _ _) le_rfl
        _ ≤ (|A| + |B| + |C|) + |E| := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    refine tri.trans ?_
    have hq2 : 0 ≤ f.q₀ ^ 2 := by positivity
    have hA' : |A| ≤ (2 * K₂ + 6 * D.K k) * f.q₀ ^ 2 := hA.trans (le_of_eq (by ring))
    have hB' : |B| ≤ (4 * D.K k * K₂ + 4 * D.K k) * f.q₀ ^ 2 :=
      hB.trans (le_of_eq (by ring))
    have hsum : |A| + |B| + |C| + |E| ≤
        (2 * K₂ + 10 * D.K k + 4 * D.K k * K₂ + 2 * D.K k ^ 2) * f.q₀ ^ 2 := by
      calc
        |A| + |B| + |C| + |E| ≤ (2 * K₂ + 6 * D.K k) * f.q₀ ^ 2 +
            (4 * D.K k * K₂ + 4 * D.K k) * f.q₀ ^ 2 + D.K k ^ 2 * f.q₀ ^ 2 +
              D.K k ^ 2 * f.q₀ ^ 2 := add_le_add (add_le_add (add_le_add hA' hB') hC) hD
        _ = _ := by ring
    refine hsum.trans (mul_le_mul_of_nonneg_right ?_ hq2)
    have hK2 : 1 ≤ D.K k ^ 2 := one_le_pow₀ hK
    have hKsq : D.K k ≤ D.K k ^ 2 := le_self_pow₀ hK (by norm_num)
    have i1 : K₂ ≤ D.K k ^ 2 * K₂ := le_mul_of_one_le_left (by linarith) hK2
    have i2 : D.K k ≤ D.K k ^ 2 * K₂ :=
      hKsq.trans (le_mul_of_one_le_right (by positivity) hK₂)
    have i3 : D.K k * K₂ ≤ D.K k ^ 2 * K₂ :=
      mul_le_mul_of_nonneg_right hKsq (by linarith)
    have i4 : D.K k ^ 2 ≤ D.K k ^ 2 * K₂ := le_mul_of_one_le_right (by positivity) hK₂
    linarith
  -- the five components
  have hq2 : 0 < f.q₀ ^ 2 := by positivity
  have hKK : D.K k ≤ D.K k ^ 2 := le_self_pow₀ hK (by norm_num)
  have hbig : D.K k ^ 2 ≤ D.K k ^ 2 * K₂ := le_mul_of_one_le_right (by positivity) hK₂
  have hK2 : 1 ≤ D.K k ^ 2 := one_le_pow₀ hK
  have j1 : K₂ ≤ D.K k ^ 2 * K₂ := le_mul_of_one_le_left (by linarith) hK2
  have j2 : D.K k ≤ D.K k ^ 2 * K₂ := hKK.trans hbig
  have hc' : (f.level h).c i = contactChartLabel f.t₀ f.q₀ f.Z₀ f.Y₀ c := rfl
  rw [hc']
  fin_cases e
  · change |(c 0 + f.t₀ * c 1 - f.Z₀) / f.q₀| ≤ _
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    refine b0.trans (mul_le_mul_of_nonneg_right ?_ hq.le)
    linarith
  · change |c 1| ≤ _
    refine (hcb 1).trans ?_
    linarith
  · change |(c 2 + f.t₀ * c 3 + c 4 * f.Z₀ - f.Y₀) / f.q₀ ^ 2| ≤ _
    rw [abs_div, abs_of_pos hq2, div_le_iff₀ hq2]
    refine b2.trans (mul_le_mul_of_nonneg_right ?_ hq2.le)
    linarith
  · change |(c 3 + f.Z₀) / f.q₀| ≤ _
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    refine b3.trans (mul_le_mul_of_nonneg_right ?_ hq.le)
    linarith
  · change |(c 4 - f.t₀) / f.q₀| ≤ _
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    refine b4.trans (mul_le_mul_of_nonneg_right ?_ hq.le)
    linarith

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
