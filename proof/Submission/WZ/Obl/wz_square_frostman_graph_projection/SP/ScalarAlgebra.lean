-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ScalarAlgebra.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealRuzsaSum
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScaledGridCount

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

noncomputable def realScalarImage (u : ℝ) (A : Finset ℝ) : Finset ℝ := A.image (fun a => u * a)

def SmallScalarProjection (δ : ℝ) (A : Finset ℝ) (K t : ℝ) : Prop :=
  RealCoverBound δ (A + realScalarImage t A) (K * (A.card : ℝ))

theorem realScalarImage_add (u : ℝ) (A B : Finset ℝ) :
    realScalarImage u (A + B) = realScalarImage u A + realScalarImage u B := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hy
    exact Finset.mem_add.mpr ⟨u * a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      u * b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, (mul_add _ _ _).symm⟩
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨a + b, Finset.add_mem_add ha hb, mul_add _ _ _⟩

theorem realScalarImage_mul (u v : ℝ) (A : Finset ℝ) :
    realScalarImage u (realScalarImage v A) = realScalarImage (u * v) A := by
  classical
  simp only [realScalarImage, Finset.image_image, Function.comp_def, mul_assoc]

theorem realScalarImage_one (A : Finset ℝ) : realScalarImage 1 A = A := by
  classical
  simp [realScalarImage]

/-- Products of positive bounded scalars with small projections again have
small projections. The loss records the smaller scalar explicitly. -/
theorem SmallScalarProjection.mul {δ u v K L : ℝ} {A : Finset ℝ}
    (hδ : 0 < δ) (hu : 0 < u) (hu1 : u ≤ 1) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hA : A.Nonempty) (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (ha : SmallScalarProjection δ A K u) (hb : SmallScalarProjection δ A L v) :
    SmallScalarProjection δ A (144 * K * L / u) (u * v) := by
  classical
  obtain ⟨m, ca, hca, hm⟩ := ha
  have hscaled : RealCoverBound δ (realScalarImage u A + realScalarImage (u * v) A)
      (L * (A.card : ℝ)) := by
    have hh := hb.scale_contract hδ.le (show |u| ≤ 1 by rwa [abs_of_pos hu])
    change RealCoverBound δ (realScalarImage u (A + realScalarImage v A)) _ at hh
    simpa only [realScalarImage_add, realScalarImage_mul] using hh
  obtain ⟨n, cb, hcb, hn⟩ := hscaled
  obtain ⟨k, centers, hc, hk⟩ := real_ruzsa_sum hδ A (realScalarImage u A)
    (realScalarImage (u * v) A) ca cb hca hcb
  refine ⟨k, centers, hc, ?_⟩
  have hG := scaled_grid_card_lower hδ hu hu1 A hsep
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hprod : (m : ℝ) * (n : ℝ) ≤ (K * (A.card : ℝ)) * (L * (A.card : ℝ)) :=
    mul_le_mul hm hn (Nat.cast_nonneg _) (by positivity)
  have hfirst : (k : ℝ) * (u * (A.card : ℝ)) ≤ 4 * ((k : ℝ) *
      ((realScalarImage u A).image (realGridIndex δ)).card) := by
    have hh := mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg k)
    dsimp only [realScalarImage]
    convert hh using 1 <;> ring
  have hlast : ((k : ℝ) * u) * (A.card : ℝ) ≤
      (144 * K * L * (A.card : ℝ)) * (A.card : ℝ) := by nlinarith [hk, hprod]
  have hcancel := (mul_le_mul_iff_left₀ hAp).mp hlast
  have hdiv := (le_div_iff₀ hu).mpr hcancel
  convert hdiv using 1 <;> field_simp <;> ring

/-- Addition of two good scalars is controlled by mixed Plunnecke, once
the unscaled sumset is also small. -/
theorem SmallScalarProjection.add {δ u v K L M : ℝ} {A : Finset ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hA : A.Nonempty) (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hbase : SmallScalarProjection δ A K 1)
    (hu : SmallScalarProjection δ A L u) (hv : SmallScalarProjection δ A M v) :
    SmallScalarProjection δ A (9 * (6 * (K + L + M)) ^ 3) (u + v) := by
  classical
  let B := A ∪ realScalarImage u A ∪ realScalarImage v A
  have hb : RealCoverBound δ (A + B) ((K + L + M) * (A.card : ℝ)) := by
    have hh := (hbase.union hu).union hv
    rw [realScalarImage_one] at hh
    convert hh using 1
    · simp only [B, Finset.add_union]
    · ring
  obtain ⟨m, cc, hc, hm⟩ := hb
  obtain ⟨n, centers, hcover, hn⟩ := mixed_plunnecke_nine hδ (by positivity) A B hA hsep cc hc hm 3 0 (by norm_num)
  norm_num only at hn
  have hsub : A + realScalarImage (u + v) A ⊆ (3 : ℕ) • B - (0 : ℕ) • B := by
    intro x hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have haB : a ∈ B := Finset.mem_union_left _ (Finset.mem_union_left _ ha)
    have huB : u * b ∈ B := Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
    have hvB : v * b ∈ B := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    have hmem := Finset.add_mem_add (Finset.add_mem_add haB huB) hvB
    simpa only [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, one_nsmul, zero_nsmul,
      sub_zero, zero_add, add_mul, add_assoc] using hmem
  exact ⟨n, centers, hcover.mono_set hsub, hn⟩

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
