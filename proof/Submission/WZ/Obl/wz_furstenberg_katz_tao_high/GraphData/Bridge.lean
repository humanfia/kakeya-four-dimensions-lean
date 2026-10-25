-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.Bridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/Bridge.lean (82de8bd).
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.AnchorCodes
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.Contradiction
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Multiscale.EndpointFinset

/-!
# From a column-dense tube to a tube model

Data at a scale `δ` in tube coordinates: lines `L` (pairs `(c, a)`, height `a + c x`), column
positions `I ⊆ [-4, 4]`, and for each column a set `Yc x` of at most `F` occupied heights.  A line
meets a column if its height there is within `δ` of an occupied height.  Assume the line/column
relation has density `d`, every column has few columns closer than `q`, columns and line
parameters are Frostman (exponents `β` and `1 + b`, constant `K₀`), lines are `9 δ / q`-separated
in parameters, heights at columns are at most `7/2`, and `F² ≤ K₀ #L`.

`tube_model_of_dense_columns`: then x0603's endpoint selection and the anchor coding produce all
inputs of `tube_model_false` (codes at the two anchors, anchor fibers, square counts, column
parameters with Frostman counts, dense column subfamilies with their fibers), with the single
constant `Kt = K₀ (9/q)^(1+b) 8^β 64 / d²` and `B = 8 / q`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The line `l` meets the column at `x` up to `δ`. -/
def Meets (Yc : ℝ → Finset ℝ) (δ : ℝ) (x : ℝ) (l : ℝ × ℝ) : Prop :=
  ∃ y ∈ Yc x, |lineHeight l x - y| ≤ δ

/-- The constant of the tube model built from column-dense data. -/
noncomputable def tubeK (K₀ q b β d : ℝ) : ℝ := K₀ * (9 / q) ^ (1 + b) * 8 ^ β * 64 / d ^ 2

theorem le_nine_mul_div {ρ q : ℝ} (hρ : 0 ≤ ρ) (hq : 0 < q) (hq1 : q ≤ 1) : ρ ≤ 9 * ρ / q := by
  rw [le_div_iff₀ hq]; nlinarith

theorem le_div_mul_of_mul_le {A B c : ℝ} (hc : 0 < c) (h : c * A ≤ B) : A ≤ 1 / c * B := by
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc]; linarith

theorem tubeK_bounds {K₀ q b β d : ℝ} (hK₀ : 1 ≤ K₀) (hq : 0 < q) (hq1 : q ≤ 1) (hb : 0 < b)
    (hβ : 0 ≤ β) (hd : 0 < d) (hd1 : d ≤ 1) :
    K₀ * (9 / q) ^ (1 + b) * (8 / d ^ 2) ≤ tubeK K₀ q b β d ∧
    K₀ * (8 / d ^ 2) ≤ tubeK K₀ q b β d ∧
    K₀ * 8 ^ β * (4 / d) ≤ tubeK K₀ q b β d ∧ 8 / d ≤ tubeK K₀ q b β d := by
  have h9q : 1 ≤ 9 / q := by rw [le_div_iff₀ hq]; linarith
  have hA : 1 ≤ (9 / q) ^ (1 + b) := Real.one_le_rpow h9q (by linarith)
  have hB : 1 ≤ (8 : ℝ) ^ β := Real.one_le_rpow (by norm_num) hβ
  have hd2 : 0 < d ^ 2 := by positivity
  have hdd : d ^ 2 ≤ d := by nlinarith
  have hK₀A : 1 ≤ K₀ * (9 / q) ^ (1 + b) := by nlinarith
  have hKAB : 1 ≤ K₀ * (9 / q) ^ (1 + b) * 8 ^ β := by nlinarith
  have hT : tubeK K₀ q b β d = K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 / d ^ 2) := by
    unfold tubeK; ring
  have h64 : 0 ≤ 64 / d ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hT]
    have h1 : K₀ * (9 / q) ^ (1 + b) * (8 / d ^ 2) ≤ K₀ * (9 / q) ^ (1 + b) * (64 / d ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (by norm_num) hd2.le
    have h2 : K₀ * (9 / q) ^ (1 + b) * (64 / d ^ 2) ≤
        K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 / d ^ 2) := by
      have e : K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 / d ^ 2) =
          (K₀ * (9 / q) ^ (1 + b) * (64 / d ^ 2)) * 8 ^ β := by ring
      rw [e]
      exact le_mul_of_one_le_right (by positivity) hB
    linarith
  · rw [hT]
    have h1 : K₀ * (8 / d ^ 2) ≤ K₀ * (64 / d ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by norm_num) hd2.le) (by linarith)
    have h2 : K₀ * (64 / d ^ 2) ≤ K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 / d ^ 2) := by
      have hp : 0 ≤ K₀ * (64 / d ^ 2) := by positivity
      have : K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 / d ^ 2) =
          (K₀ * (64 / d ^ 2)) * ((9 / q) ^ (1 + b) * 8 ^ β) := by ring
      rw [this]
      have hAB : 1 ≤ (9 / q) ^ (1 + b) * 8 ^ β := one_le_mul_of_one_le_of_one_le hA hB
      exact le_mul_of_one_le_right hp hAB
    linarith
  · rw [hT]
    have h4 : 4 / d ≤ 64 / d ^ 2 := by
      rw [div_le_div_iff₀ hd hd2]; nlinarith
    have hp : 0 ≤ K₀ * 8 ^ β := by positivity
    have h1 : K₀ * 8 ^ β * (4 / d) ≤ K₀ * 8 ^ β * (64 / d ^ 2) :=
      mul_le_mul_of_nonneg_left h4 hp
    have h2 : K₀ * 8 ^ β * (64 / d ^ 2) ≤ K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 / d ^ 2) := by
      have : K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 / d ^ 2) =
          (K₀ * 8 ^ β * (64 / d ^ 2)) * (9 / q) ^ (1 + b) := by ring
      rw [this]
      have hp2 : 0 ≤ K₀ * 8 ^ β * (64 / d ^ 2) := by positivity
      exact le_mul_of_one_le_right hp2 hA
    linarith
  · rw [hT]
    have h8 : 8 / d ≤ 64 / d ^ 2 := by
      rw [div_le_div_iff₀ hd hd2]; nlinarith
    have : 64 / d ^ 2 ≤ K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 / d ^ 2) :=
      le_mul_of_one_le_left h64 hKAB
    linarith

theorem anchorParam_abs_le {x₀ x₁ x q : ℝ} (hq : 0 < q) (hx : |x| ≤ 4) (hx₀ : |x₀| ≤ 4)
    (hgap : q ≤ |x₁ - x₀|) : |anchorParam x₀ x₁ x| ≤ 8 / q := by
  have hg : 0 < |x₁ - x₀| := lt_of_lt_of_le hq hgap
  simp only [anchorParam]
  rw [abs_div, div_le_div_iff₀ hg hq]
  have h8 : |x - x₀| ≤ 8 := by
    calc |x - x₀| ≤ |x| + |x₀| := abs_sub _ _
      _ ≤ 8 := by linarith
  have h0 : 0 ≤ |x - x₀| := abs_nonneg _
  nlinarith

theorem tube_model_of_dense_columns {δ q d F K₀ b β : ℝ}
    (hδ : 0 < δ) (hq : 0 < q) (hq1 : q ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1) (hK₀ : 1 ≤ K₀)
    (hb : 0 < b) (hβ : 0 ≤ β)
    (L : Finset (ℝ × ℝ)) (I : Finset ℝ) (Yc : ℝ → Finset ℝ)
    (hLne : L.Nonempty) (hIne : I.Nonempty) (hIb : ∀ x ∈ I, |x| ≤ 4)
    (hLb : ∀ l ∈ L, ∀ x ∈ I, |lineHeight l x| ≤ 7 / 2)
    (hLsep : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → 9 * δ / q ≤ |l.1 - l'.1| ∨ 9 * δ / q ≤ |l.2 - l'.2|)
    (hYc : ∀ x ∈ I, ((Yc x).card : ℝ) ≤ F)
    (hdens : d * (I.card : ℝ) * L.card ≤
      (((I ×ˢ L).filter (fun p => Meets Yc δ p.1 p.2)).card : ℝ))
    (hspread : ∀ x ∈ I, ((I.filter (fun x' => |x - x'| < q)).card : ℝ) ≤ d ^ 2 / 16 * I.card)
    (hIfr : ∀ z ρ : ℝ, δ ≤ ρ → ((I.filter (fun x => |x - z| ≤ ρ)).card : ℝ) ≤ K₀ * ρ ^ β * I.card)
    (hLfr : ∀ c a ρ : ℝ, δ ≤ ρ →
      ((L.filter (fun l => |l.1 - c| ≤ ρ ∧ |l.2 - a| ≤ ρ)).card : ℝ) ≤ K₀ * ρ ^ (1 + b) * L.card)
    (hquad : F ^ 2 ≤ K₀ * L.card) :
    ∃ (W : Finset (ℝ × ℝ)) (Y0 Y1 X : Finset ℝ) (Wx : ℝ → Finset (ℝ × ℝ)) (Yx : ℝ → Finset ℝ),
      W.Nonempty ∧ (∀ w ∈ W, |w.1| ≤ 7 / 2 ∧ |w.2| ≤ 7 / 2) ∧
      (∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → δ ≤ dist w w') ∧
      (Y0.card : ℝ) ≤ F ∧ (Y1.card : ℝ) ≤ F ∧
      (∀ w ∈ W, ∃ y ∈ Y0, |w.1 - y| ≤ δ) ∧ (∀ w ∈ W, ∃ y ∈ Y1, |w.2 - y| ≤ δ) ∧
      (∀ x y ρ : ℝ, δ ≤ ρ →
        ((W.filter (fun w => |w.1 - x| ≤ ρ ∧ |w.2 - y| ≤ ρ)).card : ℝ) ≤
          tubeK K₀ q b β d * ρ ^ (1 + b) * W.card) ∧
      F ^ 2 ≤ tubeK K₀ q b β d * W.card ∧
      X.Nonempty ∧ (∀ τ ∈ X, |τ| ≤ 8 / q) ∧
      (∀ x ρ : ℝ, δ ≤ ρ →
        ((X.filter (fun τ => dist τ x ≤ ρ)).card : ℝ) ≤ tubeK K₀ q b β d * ρ ^ β * X.card) ∧
      (∀ τ ∈ X, Wx τ ⊆ W) ∧ (∀ τ ∈ X, (W.card : ℝ) ≤ tubeK K₀ q b β d * (Wx τ).card) ∧
      (∀ τ ∈ X, ((Yx τ).card : ℝ) ≤ F) ∧
      (∀ τ ∈ X, ∀ w ∈ Wx τ, ∃ y ∈ Yx τ, |hgt w τ - y| ≤ δ) := by
  classical
  -- endpoint selection
  obtain ⟨x₀, hx₀, x₁, hx₁, G, hGL, S, hSI, hnb, hGR, hGcard, hScard, hS⟩ :=
    dense_endpoint_finset I L hIne hLne (fun x l => Meets Yc δ x l) (fun x x' => |x - x'| < q)
      hd hd1 hdens (fun x hx => hspread x hx)
  push Not at hnb
  have hgap : q ≤ |x₁ - x₀| := by rw [abs_sub_comm]; exact hnb
  have hne : x₀ ≠ x₁ := by
    intro h; rw [h, sub_self, abs_zero] at hgap; linarith
  have hx₀b : |x₀| ≤ 4 := hIb x₀ hx₀
  -- the code is injective on `L`
  have hcode_sep : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' →
      δ ≤ dist (anchorCode x₀ x₁ l) (anchorCode x₀ x₁ l') := by
    intro l hl l' hl' hll'
    have h := anchorCode_sep hq hq1 hgap hx₀b (hLsep l hl l' hl' hll')
    have e : q * (9 * δ / q) / 9 = δ := by field_simp
    rwa [e] at h
  have hinj : Set.InjOn (anchorCode x₀ x₁) (↑L : Set (ℝ × ℝ)) := by
    intro l hl l' hl' heq
    by_contra hll'
    have := hcode_sep l hl l' hl' hll'
    rw [heq, dist_self] at this
    linarith
  set W := G.image (anchorCode x₀ x₁) with hWdef
  have hWcard : W.card = G.card :=
    Finset.card_image_of_injOn (hinj.mono (fun l hl => hGL hl))
  have hLpos : (0 : ℝ) < L.card := by exact_mod_cast hLne.card_pos
  have hIpos : (0 : ℝ) < I.card := by exact_mod_cast hIne.card_pos
  have hGpos : (0 : ℝ) < G.card := by
    have : 0 < d ^ 2 / 8 * (L.card : ℝ) := by positivity
    linarith
  have hGne : G.Nonempty := Finset.card_pos.mp (by exact_mod_cast hGpos)
  have hSpos : (0 : ℝ) < S.card := by
    have : 0 < d / 4 * (I.card : ℝ) := by positivity
    linarith
  have hSne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hSpos)
  -- constants
  set Kt := tubeK K₀ q b β d with hKt
  obtain ⟨hKt1, hKtK₀, hKt3, hKt4⟩ := tubeK_bounds (β := β) hK₀ hq hq1 hb hβ hd hd1
  have hd2 : 0 < d ^ 2 := by positivity
  -- the anchor fibers and columns
  refine ⟨W, Yc x₀, Yc x₁, S.image (anchorParam x₀ x₁),
    fun τ => (G.filter (fun l => Meets Yc δ (x₀ + τ * (x₁ - x₀)) l)).image (anchorCode x₀ x₁),
    fun τ => Yc (x₀ + τ * (x₁ - x₀)), ?_, ?_, ?_, hYc x₀ hx₀, hYc x₁ hx₁, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact hGne.image _
  · intro w hw
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨hLb l (hGL hl) x₀ hx₀, hLb l (hGL hl) x₁ hx₁⟩
  · intro w hw w' hw' hww'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hw'
    have hll' : l ≠ l' := fun h => hww' (by rw [h])
    exact hcode_sep l (hGL hl) l' (hGL hl') hll'
  · intro w hw
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
    exact (hGR l hl).1
  · intro w hw
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
    exact (hGR l hl).2
  · -- square counts
    intro x y ρ hρ
    set c₀ := (y - x) / (x₁ - x₀) with hc₀
    set a₀ := x - c₀ * x₀ with ha₀
    have hsub : W.filter (fun w => |w.1 - x| ≤ ρ ∧ |w.2 - y| ≤ ρ) ⊆
        (L.filter (fun l => |l.1 - c₀| ≤ 9 * ρ / q ∧ |l.2 - a₀| ≤ 9 * ρ / q)).image
          (anchorCode x₀ x₁) := by
      intro w hw
      obtain ⟨hwW, hw1, hw2⟩ := by simpa using hw
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hwW
      refine Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨hGL hl, ?_⟩, rfl⟩
      have hx1' : lineHeight (c₀, a₀) x₀ = x := by
        simp only [lineHeight, ha₀]; ring
      have hne' : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hy1' : lineHeight (c₀, a₀) x₁ = y := by
        simp only [lineHeight, ha₀, hc₀]; field_simp; ring
      have hu : |lineHeight l x₀ - lineHeight (c₀, a₀) x₀| ≤ ρ := by
        rw [hx1']; simpa [anchorCode] using hw1
      have hv : |lineHeight l x₁ - lineHeight (c₀, a₀) x₁| ≤ ρ := by
        rw [hy1']; simpa [anchorCode] using hw2
      exact anchorCode_close hq hq1 hgap hx₀b hu hv
    have hρ' : δ ≤ 9 * ρ / q := hρ.trans (le_nine_mul_div (hδ.le.trans hρ) hq hq1)
    have hcount := hLfr c₀ a₀ (9 * ρ / q) hρ'
    have hρpos : 0 < ρ := lt_of_lt_of_le hδ hρ
    have e1 : (9 * ρ / q) ^ (1 + b) = (9 / q) ^ (1 + b) * ρ ^ (1 + b) := by
      rw [show 9 * ρ / q = (9 / q) * ρ by ring, Real.mul_rpow (by positivity) hρpos.le]
    have hWG : (L.card : ℝ) ≤ 8 / d ^ 2 * W.card := by
      rw [hWcard]
      have h := le_div_mul_of_mul_le (by positivity : (0 : ℝ) < d ^ 2 / 8) hGcard
      have e : 1 / (d ^ 2 / 8) = 8 / d ^ 2 := by field_simp
      rwa [e] at h
    calc ((W.filter (fun w => |w.1 - x| ≤ ρ ∧ |w.2 - y| ≤ ρ)).card : ℝ)
        ≤ (((L.filter (fun l => |l.1 - c₀| ≤ 9 * ρ / q ∧ |l.2 - a₀| ≤ 9 * ρ / q)).image
            (anchorCode x₀ x₁)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((L.filter (fun l => |l.1 - c₀| ≤ 9 * ρ / q ∧ |l.2 - a₀| ≤ 9 * ρ / q)).card : ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ ≤ K₀ * (9 * ρ / q) ^ (1 + b) * L.card := hcount
      _ = K₀ * (9 / q) ^ (1 + b) * ρ ^ (1 + b) * L.card := by rw [e1]; ring
      _ ≤ K₀ * (9 / q) ^ (1 + b) * ρ ^ (1 + b) * (8 / d ^ 2 * W.card) :=
          mul_le_mul_of_nonneg_left hWG (by positivity)
      _ = (K₀ * (9 / q) ^ (1 + b) * (8 / d ^ 2)) * ρ ^ (1 + b) * W.card := by ring
      _ ≤ Kt * ρ ^ (1 + b) * W.card := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right hKt1 (by positivity)
  · -- `F² ≤ Kt #W`
    have hWG : (L.card : ℝ) ≤ 8 / d ^ 2 * W.card := by
      rw [hWcard]
      have h := le_div_mul_of_mul_le (by positivity : (0 : ℝ) < d ^ 2 / 8) hGcard
      have e : 1 / (d ^ 2 / 8) = 8 / d ^ 2 := by field_simp
      rwa [e] at h
    calc F ^ 2 ≤ K₀ * L.card := hquad
      _ ≤ K₀ * (8 / d ^ 2 * W.card) := mul_le_mul_of_nonneg_left hWG (by linarith)
      _ = (K₀ * (8 / d ^ 2)) * W.card := by ring
      _ ≤ Kt * W.card := mul_le_mul_of_nonneg_right hKtK₀ (Nat.cast_nonneg _)
  · exact hSne.image _
  · intro τ hτ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hτ
    exact anchorParam_abs_le hq (hIb x (hSI hx)) hx₀b hgap
  · -- column Frostman
    intro z ρ hρ
    have hρpos : 0 < ρ := lt_of_lt_of_le hδ hρ
    set z' := x₀ + z * (x₁ - x₀) with hz'
    have hgap0 : 0 < |x₁ - x₀| := lt_of_lt_of_le hq hgap
    have hgap8 : |x₁ - x₀| ≤ 8 := by
      calc |x₁ - x₀| ≤ |x₁| + |x₀| := abs_sub _ _
        _ ≤ 8 := by linarith [hIb x₁ hx₁]
    have hsub : (S.image (anchorParam x₀ x₁)).filter (fun τ => dist τ z ≤ ρ) ⊆
        ((I.filter (fun x => |x - z'| ≤ 8 * ρ))).image (anchorParam x₀ x₁) := by
      intro τ hτ
      obtain ⟨hτS, hτz⟩ := Finset.mem_filter.mp hτ
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hτS
      refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hSI hx, ?_⟩, rfl⟩
      have hne' : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hxz : x - z' = (anchorParam x₀ x₁ x - z) * (x₁ - x₀) := by
        simp only [anchorParam, hz']; field_simp; ring
      rw [hxz, abs_mul]
      rw [Real.dist_eq] at hτz
      calc |anchorParam x₀ x₁ x - z| * |x₁ - x₀| ≤ ρ * 8 :=
            mul_le_mul hτz hgap8 (abs_nonneg _) hρpos.le
        _ = 8 * ρ := by ring
    have hcount := hIfr z' (8 * ρ) (by linarith)
    have hXcard : ((S.image (anchorParam x₀ x₁)).card : ℝ) = S.card := by
      rw [Finset.card_image_of_injective _ (anchorParam_injective hne)]
    have hIS : (I.card : ℝ) ≤ 4 / d * S.card := by
      have h := le_div_mul_of_mul_le (by positivity : (0 : ℝ) < d / 4) hScard
      have e : 1 / (d / 4) = 4 / d := by field_simp
      rwa [e] at h
    have e8 : (8 * ρ) ^ β = 8 ^ β * ρ ^ β := Real.mul_rpow (by norm_num) hρpos.le
    rw [hXcard]
    calc (((S.image (anchorParam x₀ x₁)).filter (fun τ => dist τ z ≤ ρ)).card : ℝ)
        ≤ (((I.filter (fun x => |x - z'| ≤ 8 * ρ)).image (anchorParam x₀ x₁)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((I.filter (fun x => |x - z'| ≤ 8 * ρ)).card : ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ ≤ K₀ * (8 * ρ) ^ β * I.card := hcount
      _ = K₀ * 8 ^ β * ρ ^ β * I.card := by rw [e8]; ring
      _ ≤ K₀ * 8 ^ β * ρ ^ β * (4 / d * S.card) :=
          mul_le_mul_of_nonneg_left hIS (by positivity)
      _ = (K₀ * 8 ^ β * (4 / d)) * ρ ^ β * S.card := by ring
      _ ≤ Kt * ρ ^ β * S.card := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right hKt3 (by positivity)
  · intro τ _ w hw
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image.mpr ⟨l, (Finset.mem_filter.mp hl).1, rfl⟩
  · intro τ hτ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hτ
    have hne' : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hxx : x₀ + anchorParam x₀ x₁ x * (x₁ - x₀) = x := by
      simp only [anchorParam]; field_simp; ring
    dsimp only
    rw [hxx]
    obtain ⟨_, _, hdeg⟩ := hS x hx
    have hcardimg : (((G.filter (fun l => Meets Yc δ x l)).image (anchorCode x₀ x₁)).card : ℝ) =
        ((G.filter (fun l => Meets Yc δ x l)).card : ℝ) := by
      rw [Finset.card_image_of_injOn (hinj.mono (fun l hl => hGL (Finset.mem_filter.mp hl).1))]
    rw [hcardimg, hWcard]
    have hG8 : (G.card : ℝ) ≤ 8 / d * ((G.filter (fun l => Meets Yc δ x l)).card : ℝ) := by
      have h := le_div_mul_of_mul_le (by positivity : (0 : ℝ) < d / 8) hdeg
      have e : 1 / (d / 8) = 8 / d := by field_simp
      rwa [e] at h
    calc (G.card : ℝ) ≤ 8 / d * ((G.filter (fun l => Meets Yc δ x l)).card : ℝ) := hG8
      _ ≤ Kt * ((G.filter (fun l => Meets Yc δ x l)).card : ℝ) :=
          mul_le_mul_of_nonneg_right hKt4 (Nat.cast_nonneg _)
  · intro τ hτ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hτ
    have hne' : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hxx : x₀ + anchorParam x₀ x₁ x * (x₁ - x₀) = x := by
      simp only [anchorParam]; field_simp; ring
    dsimp only
    rw [hxx]
    exact hYc x (hSI hx)
  · intro τ hτ w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hτ
    have hne' : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hxx : x₀ + anchorParam x₀ x₁ x * (x₁ - x₀) = x := by
      simp only [anchorParam]; field_simp; ring
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
    have hl' := (Finset.mem_filter.mp hl).2
    dsimp only
    rw [hxx] at hl' ⊢
    obtain ⟨y, hy, hly⟩ := hl'
    refine ⟨y, hy, ?_⟩
    rw [hgt_anchorCode hne]
    exact hly

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

attribute [local instance] Classical.propDecidable

/-- **Case A, in tube coordinates.**  For positive `e, b, β` there are `ζ, δ₀` such that
column-dense tube data at a scale `δ ≤ δ₀` with `F ≤ δ^(-(1-e))`, `4 ≤ δ^(-ζ/2)` and
`4 Kt (2 (1 + 8/q)²)^β 2^(1+b) ≤ δ^(-ζ)` (where `Kt = tubeK K₀ q b β d`) cannot exist. -/
theorem dense_columns_false {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ ζ δ₀ : ℝ, 0 < ζ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ ∀ (δ q d F K₀ : ℝ),
      0 < δ → δ ≤ δ₀ → 0 < q → q ≤ 1 → 0 < d → d ≤ 1 → 1 ≤ K₀ → 1 ≤ F →
      F ≤ δ ^ (-(1 - e)) →
      (4 * tubeK K₀ q b β d * (2 * (1 + 8 / q) ^ 2) ^ β) * 2 ^ (1 + b) ≤ δ ^ (-ζ) →
      4 ≤ δ ^ (-(ζ / 2)) →
      ∀ (L : Finset (ℝ × ℝ)) (I : Finset ℝ) (Yc : ℝ → Finset ℝ),
      L.Nonempty → I.Nonempty → (∀ x ∈ I, |x| ≤ 4) →
      (∀ l ∈ L, ∀ x ∈ I, |lineHeight l x| ≤ 7 / 2) →
      (∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → 9 * δ / q ≤ |l.1 - l'.1| ∨ 9 * δ / q ≤ |l.2 - l'.2|) →
      (∀ x ∈ I, ((Yc x).card : ℝ) ≤ F) →
      d * (I.card : ℝ) * L.card ≤
        (((I ×ˢ L).filter (fun p : ℝ × (ℝ × ℝ) => Meets Yc δ p.1 p.2)).card : ℝ) →
      (∀ x ∈ I, ((I.filter (fun x' => |x - x'| < q)).card : ℝ) ≤ d ^ 2 / 16 * I.card) →
      (∀ z ρ : ℝ, δ ≤ ρ → ((I.filter (fun x => |x - z| ≤ ρ)).card : ℝ) ≤ K₀ * ρ ^ β * I.card) →
      (∀ c a ρ : ℝ, δ ≤ ρ →
        ((L.filter (fun l => |l.1 - c| ≤ ρ ∧ |l.2 - a| ≤ ρ)).card : ℝ) ≤
          K₀ * ρ ^ (1 + b) * L.card) →
      F ^ 2 ≤ K₀ * L.card → False := by
  obtain ⟨ζ, δ₀, hζ, hδ₀, hδ₀2, hfalse⟩ := tube_model_false he hb hβ
  refine ⟨ζ, δ₀, hζ, hδ₀, hδ₀2, ?_⟩
  intro δ q d F K₀ hδ hδδ₀ hq hq1 hd hd1 hK₀ hF hFe hloss h4 L I Yc hLne hIne hIb hLb hLsep hYc
    hdens hspread hIfr hLfr hquad
  obtain ⟨W, Y0, Y1, X, Wx, Yx, hWne, hWb, hWsep, hY0, hY1, hW0, hW1, hsq, hWbig, hXne, hXB,
    hXfr, hWx, hWxbig, hYx, hcovx⟩ :=
    tube_model_of_dense_columns hδ hq hq1 hd hd1 hK₀ hb hβ.le L I Yc hLne hIne hIb hLb hLsep hYc
      hdens hspread hIfr hLfr hquad
  obtain ⟨_, _, _, hKt4⟩ := tubeK_bounds (β := β) hK₀ hq hq1 hb hβ.le hd hd1
  have hKt : 1 ≤ tubeK K₀ q b β d := by
    have : (1 : ℝ) ≤ 8 / d := by rw [le_div_iff₀ hd]; linarith
    linarith
  have hB : 1 ≤ 8 / q := by rw [le_div_iff₀ hq]; linarith
  exact hfalse δ F (tubeK K₀ q b β d) (8 / q) hδ hδδ₀ hB hKt hF hFe hloss h4 W hWne hWb hWsep
    Y0 Y1 hY0 hY1 hW0 hW1 hsq hWbig X hXne hXB hXfr Wx hWx hWxbig Yx hYx hcovx

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
