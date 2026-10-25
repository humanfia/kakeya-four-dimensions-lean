/-
Adapted from: here:o204
Original o204 sources and file-level provenance are recorded below.
-/
/- Original provenance: here:o204, session x0706, commit d013eb32;
   original file Submission/Obl/k4_uniform_sampled_isotropic_branches/GraphCells.lean. -/
import Submission.Lib.K4SignalMeshSupport.Terminal

/-! # Physical graph cells from base boxes and signal oscillation -/

namespace Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

open Set

noncomputable section

def baseCode (p : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℤ := fun j => ⌊z j / p⌋

def pointCode (p : ℝ) (z : Fin 3 → ℝ) (w : ℝ) : Fin 4 → ℤ :=
  Fin.snoc (baseCode p z) ⌊w / p⌋

/-- A finite BASE cover and signal oscillation over each base cell give
a physical graph cover. The base cover's exact cardinality is retained. -/
theorem graph_cells_over_base_cover {X : Type*}
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ) (A : Set X)
    {R p : ℝ} (hR : 0 ≤ R) (hp : 0 < p)
    (Base : Finset (Fin 3 → ℤ))
    (hbase : ∀ x ∈ A, baseCode p (Z x) ∈ Base)
    (hosc : ∀ x ∈ A, ∀ y ∈ A, baseCode p (Z x) = baseCode p (Z y) →
      |signal x - signal y| ≤ R * p) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) ≤ (Base.card : ℝ) * (2 * R + 2) ∧
      ∀ x ∈ A, pointCode p (Z x) (signal x) ∈ S := by
  classical
  obtain ⟨G, hG, hcover⟩ := Submission.Lib.K4SignalMeshSupport.terminal_support_of_fiber_oscillation
    A (fun x => baseCode p (Z x)) signal Base hp hR hbase hosc
  let pack (q : (Fin 3 → ℤ) × ℤ) : Fin 4 → ℤ := Fin.snoc q.1 q.2
  refine ⟨G.image pack, ?_, ?_⟩
  · exact (show (((G.image pack).card : ℝ)) ≤ (G.card : ℝ) by
      exact_mod_cast Finset.card_image_le).trans hG
  · intro x hx
    exact Finset.mem_image.mpr ⟨(baseCode p (Z x), ⌊signal x / p⌋), hcover x hx, rfl⟩

/-- A rectangular base box pays the PRODUCT of its side lengths. -/
theorem graph_cells_of_rectangular_fiber_oscillation {X : Type*}
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ) (A : Set X) (c H : Fin 3 → ℝ)
    {R p : ℝ} (hH : ∀ j, 0 ≤ H j) (hR : 0 ≤ R) (hp : 0 < p)
    (hbox : ∀ x ∈ A, ∀ j, |Z x j - c j| ≤ H j)
    (hosc : ∀ x ∈ A, ∀ y ∈ A, baseCode p (Z x) = baseCode p (Z y) →
      |signal x - signal y| ≤ R * p) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) ≤ (∏ j : Fin 3, (4 * H j / p + 2)) * (2 * R + 2) ∧
      ∀ x ∈ A, pointCode p (Z x) (signal x) ∈ S := by
  classical
  choose B hB hmem using fun j : Fin 3 =>
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hp (hH j) (c j)
  let Base := Fintype.piFinset B
  have hbase (x : X) (hx : x ∈ A) : baseCode p (Z x) ∈ Base :=
    Fintype.mem_piFinset.mpr (fun j => hmem j (Z x j) (hbox x hx j))
  have hcardBase : (Base.card : ℝ) ≤ ∏ j : Fin 3, (4 * H j / p + 2) := by
    simp only [Base, Fintype.card_piFinset, Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hB j)
  obtain ⟨S, hS, hcover⟩ := graph_cells_over_base_cover Z signal A hR hp Base hbase hosc
  exact ⟨S, hS.trans (mul_le_mul_of_nonneg_right hcardBase (by positivity)), hcover⟩

/-- The previous scalar-width API is the equal-side special case. -/
theorem graph_cells_of_fiber_oscillation {X : Type*}
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ) (A : Set X) (c : Fin 3 → ℝ)
    {H R p : ℝ} (hH : 0 ≤ H) (hR : 0 ≤ R) (hp : 0 < p)
    (hbox : ∀ x ∈ A, ∀ j, |Z x j - c j| ≤ H)
    (hosc : ∀ x ∈ A, ∀ y ∈ A, baseCode p (Z x) = baseCode p (Z y) →
      |signal x - signal y| ≤ R * p) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) ≤ (4 * H / p + 2) ^ 3 * (2 * R + 2) ∧
      ∀ x ∈ A, pointCode p (Z x) (signal x) ∈ S := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    graph_cells_of_rectangular_fiber_oscillation Z signal A c (fun _ => H)
      (fun _ => hH) hR hp hbox hosc

/-- If the physical mesh resolves the packet's base width, its cells have
total mesh volume bounded by a constant times the base volume. -/
theorem graph_cells_volume {X : Type*}
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ) (A : Set X) (c : Fin 3 → ℝ)
    {H R p : ℝ} (hR : 0 ≤ R) (hp : 0 < p) (hpH : p ≤ H)
    (hbox : ∀ x ∈ A, ∀ j, |Z x j - c j| ≤ H)
    (hosc : ∀ x ∈ A, ∀ y ∈ A, baseCode p (Z x) = baseCode p (Z y) →
      |signal x - signal y| ≤ R * p) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * p ^ 3 ≤ 216 * H ^ 3 * (2 * R + 2) ∧
      ∀ x ∈ A, pointCode p (Z x) (signal x) ∈ S := by
  have hH : 0 ≤ H := hp.le.trans hpH
  obtain ⟨S, hcard, hcover⟩ := graph_cells_of_fiber_oscillation Z signal A c
    hH hR hp hbox hosc
  have hside : 4 * H / p + 2 ≤ 6 * H / p := by
    apply (le_div_iff₀ hp).mpr
    field_simp
    nlinarith
  refine ⟨S, ?_, hcover⟩
  calc
    (S.card : ℝ) * p ^ 3 ≤ ((6 * H / p) ^ 3 * (2 * R + 2)) * p ^ 3 := by
      gcongr
      exact hcard.trans (by gcongr)
    _ = _ := by field_simp <;> ring

/-- Once the mesh resolves every side, its graph mesh volume costs
the rectangular base volume, including only ONE factor per narrow axis. -/
theorem graph_cells_rectangular_volume {X : Type*}
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ) (A : Set X) (c H : Fin 3 → ℝ)
    {R p : ℝ} (hR : 0 ≤ R) (hp : 0 < p) (hpH : ∀ j, p ≤ H j)
    (hbox : ∀ x ∈ A, ∀ j, |Z x j - c j| ≤ H j)
    (hosc : ∀ x ∈ A, ∀ y ∈ A, baseCode p (Z x) = baseCode p (Z y) →
      |signal x - signal y| ≤ R * p) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * p ^ 3 ≤ 216 * (∏ j, H j) * (2 * R + 2) ∧
      ∀ x ∈ A, pointCode p (Z x) (signal x) ∈ S := by
  have hH (j : Fin 3) : 0 ≤ H j := hp.le.trans (hpH j)
  obtain ⟨S, hS, hcover⟩ := graph_cells_of_rectangular_fiber_oscillation
    Z signal A c H hH hR hp hbox hosc
  have hside (j : Fin 3) : 4 * H j / p + 2 ≤ 6 * H j / p := by
    apply (le_div_iff₀ hp).mpr
    field_simp
    nlinarith [hpH j]
  have hprod : (∏ j : Fin 3, (4 * H j / p + 2)) ≤ ∏ j : Fin 3, (6 * H j / p) :=
    Finset.prod_le_prod₀ (fun j _ => by have := hH j; positivity) (fun j _ => hside j)
  refine ⟨S, ?_, hcover⟩
  calc
    (S.card : ℝ) * p ^ 3 ≤ ((∏ j : Fin 3, (6 * H j / p)) * (2 * R + 2)) * p ^ 3 :=
      mul_le_mul_of_nonneg_right
        (hS.trans (mul_le_mul_of_nonneg_right hprod (by positivity))) (by positivity)
    _ = _ := by simp only [Fin.prod_univ_three]; field_simp; ring

/-- Moving rectangular boxes use the accepted exact base-volume cover;
no largest-side cube is introduced. -/
theorem graph_cells_moving_volume {X : Type*}
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ) (A : Set X)
    {R p radius L : ℝ} (hR : 0 ≤ R) (hp : 0 < p) (hpr : p ≤ radius) (hL : 0 ≤ L)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hpw : ∀ i, p ≤ width i)
    (hmove : ∀ i, L * p ≤ width i)
    (hbox : ∀ x ∈ A, Z x ∈
      Submission.Lib.K4MovingMeshBoxes.movingBox time radius center velocity width)
    (hosc : ∀ x ∈ A, ∀ y ∈ A, baseCode p (Z x) = baseCode p (Z y) →
      |signal x - signal y| ≤ R * p) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * p ^ 3 ≤ 600 * radius * width 0 * width 1 * (2 * R + 2) ∧
      ∀ x ∈ A, pointCode p (Z x) (signal x) ∈ S := by
  obtain ⟨Base, hBase, hcover⟩ := Submission.Lib.K4MovingMeshBoxes.movingBox_mesh_volume
    hp hpr hL time center velocity width hv hpw hmove
  obtain ⟨S, hS, hcoverS⟩ := graph_cells_over_base_cover Z signal A hR hp Base
    (fun x hx => hcover _ (hbox x hx)) hosc
  refine ⟨S, ?_, hcoverS⟩
  calc
    (S.card : ℝ) * p ^ 3 ≤ ((Base.card : ℝ) * (2 * R + 2)) * p ^ 3 :=
      mul_le_mul_of_nonneg_right hS (by positivity)
    _ = ((Base.card : ℝ) * p ^ 3) * (2 * R + 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hBase (by positivity)

end

end Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
