-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.LinearityApply.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityPlane
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.Normalization
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.BoundedSlope

/-!
# Applying the dichotomy to dot-product triples (sticky Lemma 5.3, conclusion)

Given `DotTriples` and one instance of `LinearityDichotomy`, we find a linear function `L` with
`|f (ρ k) - L (ρ k)| ≤ ρ / 8` on at least `δ^{ε-1}` layers `k` of the triples.

The plane points are `a k = A_e (x k, y k)` with `x k = (ρ k - ρ k0) / s`,
`y k = (f (ρ k) - f (ρ k0)) / s`, and `b j = B_e (-μ g j, μ Y j) / 4 + (1/2, 1/2)`, where
`A_e (x, y) = ((e x + y)/2, (e x - y)/2)` and `B_e (u, v) = (e u + v, e u - v)` preserve dot
products, `e = ±1` selecting the half of the triples on one side of `k0`.
-/

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset Set Metric
open scoped RealInnerProductSpace

noncomputable section

open Classical in
/-- One instance of `LinearityDichotomy` (fixed `σ, ε, η, δ`). -/
def LDInstance (σ ε η δ : ℝ) : Prop :=
  ∀ (Ks Js : Finset ℤ) (a b : ℤ → Plane) (T : Finset (ℤ × ℤ × ℤ)) (D : Set ℝ),
    (∀ k ∈ Ks, a k ∈ unitSquare) → (∀ j ∈ Js, b j ∈ unitSquare) →
    ∀ N₀ : ℝ, 1 ≤ N₀ → (∀ k ∈ Ks, (#(Ks.filter fun k' => dist (a k) (a k') ≤ 2 * δ) : ℝ) ≤ N₀) →
    (∀ j ∈ Js, (#(Js.filter fun j' => dist (b j) (b j') ≤ 2 * δ) : ℝ) ≤ N₀) →
    ADset δ 1 (δ ^ (-η)) (a '' Ks) → ADset δ 1 (δ ^ (-η)) (b '' Js) →
    T ⊆ Ks ×ˢ Js ×ˢ Js → N₀ ^ 3 * δ ^ (η - 3) ≤ #T →
    Assouad δ (1 - σ) (δ ^ (-η)) D →
    (∀ t ∈ T, ⟪a t.1, b t.2.1 - b t.2.2⟫ ∈ D) →
    ∃ p d : Plane, d ≠ 0 ∧
      δ ^ (ε - 1) ≤ #(Ks.filter fun k => a k ∈ thickening δ (lineThrough p d))

theorem LinearityDichotomy.instance {σ : ℝ} (h : LinearityDichotomy σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → LDInstance σ ε η δ := by
  obtain ⟨η, δ₀, hη, hδ₀, hH⟩ := h ε hε
  refine ⟨η, δ₀, hη, hδ₀, fun δ hδ hδδ => ?_⟩
  intro Ks Js a b T D h1 h2 N₀ hN₀ h3 h4 h5 h6 h7 h8 h9 h10
  classical
  convert hH δ hδ hδδ Ks Js a b T D h1 h2 N₀ hN₀ h3 h4 h5 h6 h7 h8 h9 h10 using 6

/-- A point of the plane from its coordinates. -/
def pt (u v : ℝ) : Plane := WithLp.toLp 2 ![u, v]

@[simp] theorem pt_zero (u v : ℝ) : pt u v 0 = u := by simp [pt]
@[simp] theorem pt_one (u v : ℝ) : pt u v 1 = v := by simp [pt]

theorem dist_pt_sq (u v u' v' : ℝ) : dist (pt u v) (pt u' v') ^ 2 = (u - u') ^ 2 + (v - v') ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

theorem inner_pt (u v u' v' : ℝ) : ⟪pt u v, pt u' v'⟫ = u * u' + v * v' := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, pt_zero, pt_one, RCLike.inner_apply,
    conj_trivial]
  ring

theorem pt_sub (u v u' v' : ℝ) : pt u v - pt u' v' = pt (u - u') (v - v') := by
  ext i; fin_cases i <;> simp [pt]

theorem pt_add (u v u' v' : ℝ) : pt u v + pt u' v' = pt (u + u') (v + v') := by
  ext i; fin_cases i <;> simp [pt]

theorem pt_smul (t u v : ℝ) : t • pt u v = pt (t * u) (t * v) := by
  ext i; fin_cases i <;> simp [pt]

theorem pt_eta (p : Plane) : pt (p 0) (p 1) = p := by
  ext i; fin_cases i <;> simp [pt]

theorem le_dist_pt_of_abs_le {u v u' v' c : ℝ} (h : c ≤ |u - u'|) (hc : 0 ≤ c) :
    c ≤ dist (pt u v) (pt u' v') := by
  have h2 := dist_pt_sq u v u' v'
  have : c ^ 2 ≤ dist (pt u v) (pt u' v') ^ 2 := by
    rw [h2]; nlinarith [sq_abs (u - u'), sq_nonneg (v - v'), abs_nonneg (u - u')]
  exact (pow_le_pow_iff_left₀ hc dist_nonneg (by norm_num)).mp this

theorem dist_pt_le (u v u' v' : ℝ) : dist (pt u v) (pt u' v') ≤ |u - u'| + |v - v'| := by
  have h2 := dist_pt_sq u v u' v'
  have : dist (pt u v) (pt u' v') ^ 2 ≤ (|u - u'| + |v - v'|) ^ 2 := by
    rw [h2]; nlinarith [sq_abs (u - u'), sq_abs (v - v'), abs_nonneg (u - u'),
      abs_nonneg (v - v'), mul_nonneg (abs_nonneg (u - u')) (abs_nonneg (v - v'))]
  exact (pow_le_pow_iff_left₀ dist_nonneg (by positivity) (by norm_num)).mp this

/-- The thickening of an Assouad-type set, rescaled, is Assouad-type at the coarser scale. -/
theorem assouad_dotSet {ρ α K w lam δ η : ℝ} {B : Set ℝ} (hρ : 0 < ρ) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hK : 0 ≤ K) (hB : Assouad ρ α K B) (hlam : 0 < lam)
    (hscale : lam * (4 * ρ) ≤ δ) (hconst : 6 * K ≤ δ ^ (-η)) (hδ : 0 < δ) :
    Assouad δ α (δ ^ (-η))
      ((fun x => lam * x + 0) '' {x | ∃ v ∈ B, |x - (v - w * ρ)| ≤ 4 * ρ}) := by
  have h1 : Assouad (1 * ρ) α K ((fun x => 1 * x + (-(w * ρ))) '' B) :=
    Assouad.affine_image hρ one_pos hB
  rw [one_mul] at h1
  have h2 : Assouad (4 * ρ) α K ((fun x => 1 * x + (-(w * ρ))) '' B) :=
    Assouad.mono_scale h1 (by linarith)
  have h3 : Assouad (4 * ρ) α (6 * K) {x | ∃ v ∈ B, |x - (v - w * ρ)| ≤ 4 * ρ} := by
    apply Assouad.perturb (by linarith) hα0 hα1 hK h2
    rintro x ⟨v, hv, hxv⟩
    exact ⟨1 * v + (-(w * ρ)), ⟨v, hv, rfl⟩, by rw [one_mul, ← sub_eq_add_neg]; exact hxv⟩
  have h4 := Assouad.affine_image (a := lam) (b := 0) (by linarith) hlam h3
  exact Assouad.mono_constant hδ (Assouad.mono_scale h4 hscale) hconst

/-- `AD` constants are monotone. -/
theorem ADset.mono_constant {E : Type*} [PseudoMetricSpace E] {δ α C C' : ℝ} {X : Set E}
    (h : ADset δ α C X) (hCC : C ≤ C') (hδ : 0 < δ) : ADset δ α C' X := by
  intro x ρ r hδρ hρr
  obtain ⟨m, c, hc, hm⟩ := h x ρ r hδρ hρr
  have hρ : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have : 0 ≤ (r / ρ) ^ α := Real.rpow_nonneg (div_nonneg (le_trans hρ.le hρr) hρ.le) _
  exact ⟨m, c, hc, hm.trans (by gcongr)⟩

/-- Half of the triples lie on one side of `k0`. -/
theorem exists_half (T : Finset (ℤ × ℤ × ℤ)) (k0 : ℤ) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∃ Te ⊆ T, (#T : ℝ) ≤ 2 * #Te ∧
      ∀ t ∈ Te, 0 ≤ e * ((t.1 : ℝ) - k0) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun t => k0 ≤ t.1)
  have hR : (#(T.filter fun t => k0 ≤ t.1) : ℝ) + #(T.filter fun t => ¬ k0 ≤ t.1) = #T := by
    exact_mod_cast hsplit
  by_cases h : (#T : ℝ) ≤ 2 * #(T.filter fun t => k0 ≤ t.1)
  · refine ⟨1, Or.inl rfl, T.filter fun t => k0 ≤ t.1, Finset.filter_subset _ _, h, ?_⟩
    intro t ht
    have := (Finset.mem_filter.mp ht).2
    have : (k0 : ℝ) ≤ t.1 := by exact_mod_cast this
    linarith
  · refine ⟨-1, Or.inr rfl, T.filter fun t => ¬ k0 ≤ t.1, Finset.filter_subset _ _, ?_, ?_⟩
    · linarith
    · intro t ht
      have := (Finset.mem_filter.mp ht).2
      have : (t.1 : ℝ) < k0 := by exact_mod_cast lt_of_not_ge this
      linarith

/-- **Line analysis.** Points `(x k, y k)` of a `1`-Lipschitz graph with `x`-separation `sep`,
each within `2δ` (coordinatewise) of a common line `P + t d`, number at most one if the line is
steep; otherwise they are within `6δ` vertically of the line of slope `d1 / d0`, `|d1/d0| ≤ 2`. -/
theorem line_analysis {S : Finset ℤ} {x y : ℤ → ℝ} {P0 P1 d0 d1 δ sep : ℝ}
    (hsep : ∀ k ∈ S, ∀ k' ∈ S, k ≠ k' → sep ≤ |x k - x k'|)
    (hlip : ∀ k ∈ S, ∀ k' ∈ S, |y k - y k'| ≤ |x k - x k'|)
    (hnear : ∀ k ∈ S, ∃ t : ℝ, |x k - (P0 + t * d0)| < 2 * δ ∧ |y k - (P1 + t * d1)| < 2 * δ)
    (hd : d0 ≠ 0 ∨ d1 ≠ 0) (hδsep : 12 * δ ≤ sep) (hS : 1 < #S) :
    d0 ≠ 0 ∧ |d1 / d0| ≤ 2 ∧ ∀ k ∈ S, |y k - (P1 + d1 / d0 * (x k - P0))| < 6 * δ := by
  classical
  -- steep lines carry at most one point
  have hshallow : |d1| ≤ 2 * |d0| := by
    by_contra hsteep
    push Not at hsteep
    have hle : #S ≤ 1 := by
      rw [Finset.card_le_one]
      intro k hk k' hk'
      by_contra hne
      obtain ⟨t, ht1, ht2⟩ := hnear k hk
      obtain ⟨t', ht1', ht2'⟩ := hnear k' hk'
      have hs := hsep k hk k' hk' hne
      have hl := hlip k hk k' hk'
      have e1 : |(x k - x k') - (t - t') * d0| < 4 * δ := by
        have : (x k - x k') - (t - t') * d0 = (x k - (P0 + t * d0)) - (x k' - (P0 + t' * d0)) := by
          ring
        rw [this]
        calc _ ≤ |x k - (P0 + t * d0)| + |x k' - (P0 + t' * d0)| := abs_sub _ _
          _ < 2 * δ + 2 * δ := add_lt_add ht1 ht1'
          _ = 4 * δ := by ring
      have e2 : |(y k - y k') - (t - t') * d1| < 4 * δ := by
        have : (y k - y k') - (t - t') * d1 = (y k - (P1 + t * d1)) - (y k' - (P1 + t' * d1)) := by
          ring
        rw [this]
        calc _ ≤ |y k - (P1 + t * d1)| + |y k' - (P1 + t' * d1)| := abs_sub _ _
          _ < 2 * δ + 2 * δ := add_lt_add ht2 ht2'
          _ = 4 * δ := by ring
      have hA : |t - t'| * |d1| < |x k - x k'| + 4 * δ := by
        have : |(t - t') * d1| ≤ |y k - y k'| + |(y k - y k') - (t - t') * d1| := by
          calc |(t - t') * d1| = |(y k - y k') - ((y k - y k') - (t - t') * d1)| := by ring_nf
            _ ≤ |y k - y k'| + |(y k - y k') - (t - t') * d1| := abs_sub _ _
        rw [abs_mul] at this
        linarith
      have hB : |x k - x k'| < |t - t'| * |d0| + 4 * δ := by
        have : |x k - x k'| ≤ |(t - t') * d0| + |(x k - x k') - (t - t') * d0| := by
          calc |x k - x k'| = |(t - t') * d0 + ((x k - x k') - (t - t') * d0)| := by ring_nf
            _ ≤ |(t - t') * d0| + |(x k - x k') - (t - t') * d0| := abs_add_le _ _
        rw [abs_mul] at this
        linarith
      have hT0 : 0 ≤ |t - t'| := abs_nonneg _
      have hst : |t - t'| * (2 * |d0|) ≤ |t - t'| * |d1| :=
        mul_le_mul_of_nonneg_left hsteep.le hT0
      have hC : |t - t'| * |d0| < 8 * δ := by nlinarith [abs_nonneg d0, abs_nonneg d1]
      linarith
    omega
  have hd0 : d0 ≠ 0 := by
    rcases hd with h0 | h1
    · exact h0
    · intro h0
      rw [h0, abs_zero, mul_zero] at hshallow
      exact h1 (abs_nonpos_iff.mp hshallow)
  refine ⟨hd0, ?_, ?_⟩
  · rw [abs_div, div_le_iff₀ (abs_pos.mpr hd0)]; exact hshallow
  · intro k hk
    obtain ⟨t, ht1, ht2⟩ := hnear k hk
    have e : y k - (P1 + d1 / d0 * (x k - P0)) =
        (y k - (P1 + t * d1)) - d1 / d0 * (x k - (P0 + t * d0)) := by
      field_simp; ring
    rw [e]
    have hm : |d1 / d0| ≤ 2 := by
      rw [abs_div, div_le_iff₀ (abs_pos.mpr hd0)]; exact hshallow
    calc |(y k - (P1 + t * d1)) - d1 / d0 * (x k - (P0 + t * d0))|
        ≤ |y k - (P1 + t * d1)| + |d1 / d0 * (x k - (P0 + t * d0))| := abs_sub _ _
      _ = |y k - (P1 + t * d1)| + |d1 / d0| * |x k - (P0 + t * d0)| := by rw [abs_mul]
      _ < 2 * δ + 2 * (2 * δ) := by
          have h0 : 0 ≤ |x k - (P0 + t * d0)| := abs_nonneg _
          nlinarith [abs_nonneg (d1 / d0)]
      _ = 6 * δ := by ring

end

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
