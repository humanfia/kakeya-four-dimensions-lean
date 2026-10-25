import Submission.Lib.K4IncidenceWitnesses

/-!
Adapted from: here:o202

Finite-mesh comparison for affine fits, using the original measure's occupied
cells. The box bound is E*(1+48*C/m) when cells of side 1/H have mass at most
C/H^3, total mass is at least m, and H*m >= 30*C. No continuous base density
is assumed. Observed points and all comparison points lie in the unit cube.
-/

namespace Submission.Lib.K4AffineMesh

open MeasureTheory Set

/-- A three-dimensional integer grid meets an affine slab in at most a
surface-order number of cells, with the thickness measured in one nonzero coefficient. -/
lemma affine_grid_slab_card {H : ℕ} (S : Finset (Fin 3 → Fin H))
    {a₀ a₁ a₂ c E : ℝ} (ha₀ : a₀ ≠ 0) (hE : 0 ≤ E)
    (hfit : ∀ p ∈ S, |c + a₀ * (p 0 : ℕ) + a₁ * (p 1 : ℕ) + a₂ * (p 2 : ℕ)| ≤ E) :
    (S.card : ℝ) ≤ H ^ 2 * (4 * E / |a₀| + 3) := by
  classical
  let φ : (Fin 3 → Fin H) → Fin H × Fin H := fun p => (p 1, p 2)
  let F : (Fin H × Fin H) → Finset (Fin 3 → Fin H) :=
    fun r => S.filter (fun p => φ p = r)
  have hpair {p q : Fin 3 → Fin H} {r : Fin H × Fin H}
      (hp : p ∈ F r) (hq : q ∈ F r) : p 1 = q 1 ∧ p 2 = q 2 := by
    have heq := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  have hfiber (r : Fin H × Fin H) : (F r).card ≤ (2 * (2 * E / |a₀|) + 3 : ℝ) := by
    have hinj : Set.InjOn (fun p : Fin 3 → Fin H => p 0) (F r) := by
      intro p hp q hq h0
      obtain ⟨h1, h2⟩ := hpair hp hq
      apply funext
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    let G := (F r).image (fun p => p 0)
    let g : Fin H → Fin 1 → ℤ := fun u _ => (u : ℕ)
    have hginj : Function.Injective g := by
      intro u v huv
      apply Fin.ext
      exact Int.ofNat_inj.mp (congrFun huv 0)
    have hdiam : ∀ u ∈ G.image g, ∀ v ∈ G.image g, ∀ j,
        |(u j : ℝ) - (v j : ℝ)| ≤ 2 * E / |a₀| := by
      rintro U hU V hV j
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hU
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hV
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨h1, h2⟩ := hpair hp hq
      have heq : a₀ * ((p 0 : ℕ) - (q 0 : ℕ) : ℝ) =
          (c + a₀ * (p 0 : ℕ) + a₁ * (p 1 : ℕ) + a₂ * (p 2 : ℕ)) -
          (c + a₀ * (q 0 : ℕ) + a₁ * (q 1 : ℕ) + a₂ * (q 2 : ℕ)) := by
        rw [h1, h2]
        ring
      have hd : |((p 0 : ℕ) : ℝ) - ((q 0 : ℕ) : ℝ)| ≤ 2 * E / |a₀| := by
        apply (le_div_iff₀ (abs_pos.mpr ha₀)).mpr
        rw [mul_comm, ← abs_mul, heq]
        exact (abs_sub _ _).trans (by
          linarith [hfit p (Finset.mem_filter.mp hp).1,
            hfit q (Finset.mem_filter.mp hq).1])
      simpa only [g, Int.cast_natCast] using hd
    have hb := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter
      (G.image g) (by positivity) hdiam
    have hcard : (G.image g).card = (F r).card := by
      rw [Finset.card_image_of_injective _ hginj]
      exact Finset.card_image_of_injOn hinj
    simpa only [hcard, Fintype.card_fin, pow_one] using hb
  have hcount : S.card = ∑ r ∈ S.image φ, (F r).card := by
    have h := Finset.sum_card_fiberwise_eq_card_filter S (S.image φ) φ
    rw [Finset.filter_eq_self.mpr (fun p hp => Finset.mem_image_of_mem φ hp)] at h
    exact h.symm
  have hproj : ((S.image φ).card : ℝ) ≤ H ^ 2 := by
    have h := Finset.card_le_univ (s := S.image φ)
    simpa [pow_two] using (Nat.cast_le (α := ℝ)).mpr h
  have hsize : 0 ≤ 2 * (2 * E / |a₀|) + 3 := by positivity
  calc (S.card : ℝ) = ∑ r ∈ S.image φ, ((F r).card : ℝ) := by
        rw [hcount, Nat.cast_sum]
    _ ≤ ∑ _r ∈ S.image φ, (2 * (2 * E / |a₀|) + 3) :=
        Finset.sum_le_sum (fun r _ => hfiber r)
    _ = ((S.image φ).card : ℝ) * (2 * (2 * E / |a₀|) + 3) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ H ^ 2 * (2 * (2 * E / |a₀|) + 3) := mul_le_mul_of_nonneg_right hproj hsize
    _ = _ := by ring

/-- A finite mesh cap and enough occupied cells bound a nonzero dominant
slope. The grid fit includes the three-coordinate rounding error. -/
lemma affine_mesh_slope_bound {H : ℕ} (hH : 0 < H) (S : Finset (Fin 3 → Fin H))
    {a₀ a₁ a₂ c E C m : ℝ} (ha₀ : a₀ ≠ 0) (hE : 0 ≤ E) (hC : 0 ≤ C) (hm : 0 < m)
    (hmass : m ≤ C / (H : ℝ) ^ 3 * S.card)
    (hfine : 30 * C ≤ m * H)
    (hfit : ∀ p ∈ S,
      |(H : ℝ) * c + a₀ * (p 0 : ℕ) + a₁ * (p 1 : ℕ) + a₂ * (p 2 : ℕ)| ≤
        H * E + 3 * |a₀|) :
    |a₀| ≤ 8 * C * E / m := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hA : 0 < |a₀| := abs_pos.mpr ha₀
  have hgrid := affine_grid_slab_card S ha₀ (by positivity) hfit
  have hcap := hmass.trans (mul_le_mul_of_nonneg_left hgrid
    (by positivity : 0 ≤ C / (H : ℝ) ^ 3))
  have hmul := mul_le_mul_of_nonneg_right hcap
    (by positivity : 0 ≤ (H : ℝ) * |a₀|)
  have heq : (C / (H : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
        (4 * (H * E + 3 * |a₀|) / |a₀| + 3))) * (H * |a₀|) =
      C * (4 * (H * E + 3 * |a₀|) + 3 * |a₀|) := by
    field_simp
  rw [heq] at hmul
  have hfine' := mul_le_mul_of_nonneg_right hfine (abs_nonneg a₀)
  have hbound : m * H * |a₀| ≤ 8 * C * H * E := by nlinarith
  apply (le_div_iff₀ hm).mpr
  apply (mul_le_mul_iff_right₀ hH').mp
  nlinarith [hbound]

/-- Pointwise affine fits extend to the integer representatives of occupied
cells, with only the three coordinate-rounding errors. -/
lemma affine_grid_rounding_bound {H : ℕ} (p : Fin 3 → Fin H) (x a : Fin 3 → ℝ)
    (c A E : ℝ) (hA : 0 ≤ A) (ha : ∀ j, |a j| ≤ A)
    (hround : ∀ j, |(p j : ℕ) - (H : ℝ) * x j| ≤ 1)
    (hfit : |c + ∑ j, a j * x j| ≤ E) :
    |(H : ℝ) * c + ∑ j, a j * (p j : ℕ)| ≤ H * E + 3 * A := by
  have hterm (j : Fin 3) : |a j * ((p j : ℕ) - (H : ℝ) * x j)| ≤ A := by
    rw [abs_mul]
    simpa using mul_le_mul (ha j) (hround j) (abs_nonneg _) hA
  have hsum : |∑ j, a j * ((p j : ℕ) - (H : ℝ) * x j)| ≤ 3 * A := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : Fin 3, |a j * ((p j : ℕ) - (H : ℝ) * x j)| ≤ ∑ _j : Fin 3, A :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = 3 * A := by simp
  have hbase : |(H : ℝ) * (c + ∑ j, a j * x j)| ≤ H * E := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg H)]
    exact mul_le_mul_of_nonneg_left hfit (Nat.cast_nonneg H)
  have heq : (H : ℝ) * c + ∑ j, a j * (p j : ℕ) =
      H * (c + ∑ j, a j * x j) + ∑ j, a j * ((p j : ℕ) - (H : ℝ) * x j) := by
    simp only [Fin.sum_univ_succ]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hbase hsum)

/-- The mesh slope estimate with actual observation points in each occupied cell. -/
lemma affine_slope_bound_of_mesh_witnesses {H : ℕ} (hH : 0 < H)
    (S : Finset (Fin 3 → Fin H)) (a : Fin 3 → ℝ)
    (w : (Fin 3 → Fin H) → Fin 3 → ℝ) {c E C m : ℝ}
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hm : 0 < m)
    (hmass : m ≤ C / (H : ℝ) ^ 3 * S.card) (hfine : 30 * C ≤ m * H)
    (hmax : ∀ j, |a j| ≤ |a 0|)
    (hround : ∀ p ∈ S, ∀ j, |(p j : ℕ) - (H : ℝ) * w p j| ≤ 1)
    (hfit : ∀ p ∈ S, |c + ∑ j, a j * w p j| ≤ E) :
    |a 0| ≤ 8 * C * E / m := by
  by_cases hz : a 0 = 0
  · rw [hz, abs_zero]
    positivity
  apply affine_mesh_slope_bound hH S hz hE hC hm hmass hfine
    (a₁ := a 1) (a₂ := a 2) (c := c)
  intro p hp
  have h := affine_grid_rounding_bound p (w p) a c |a 0| E
    (abs_nonneg _) hmax (hround p hp) (hfit p hp)
  simpa [Fin.sum_univ_succ, add_assoc] using h

/-- Finite mesh caps suffice for full affine box comparison. This uses actual
occupied-cell witnesses and no continuous base-density hypothesis. Coordinate
zero is chosen to have maximal slope after normalizing the box. -/
lemma affine_box_bound_of_mesh_witnesses {H : ℕ} (hH : 0 < H)
    (S : Finset (Fin 3 → Fin H)) (a : Fin 3 → ℝ)
    (w : (Fin 3 → Fin H) → Fin 3 → ℝ) {c E C m : ℝ}
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hm : 0 < m)
    (hmass : m ≤ C / (H : ℝ) ^ 3 * S.card) (hfine : 30 * C ≤ m * H)
    (hmax : ∀ j, |a j| ≤ |a 0|)
    (hw : ∀ p ∈ S, ∀ j, |w p j| ≤ 1)
    (hround : ∀ p ∈ S, ∀ j, |(p j : ℕ) - (H : ℝ) * w p j| ≤ 1)
    (hfit : ∀ p ∈ S, |c + ∑ j, a j * w p j| ≤ E)
    (z : Fin 3 → ℝ) (hz : ∀ j, |z j| ≤ 1) :
    |c + ∑ j, a j * z j| ≤ E + 48 * C * E / m := by
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty, Nat.cast_zero, mul_zero] at hmass
    linarith
  obtain ⟨p, hp⟩ := hS
  have hslope := affine_slope_bound_of_mesh_witnesses hH S a w hE hC hm hmass hfine
    hmax hround hfit
  have hlin (x : Fin 3 → ℝ) (hx : ∀ j, |x j| ≤ 1) :
      |∑ j, a j * x j| ≤ 3 * |a 0| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : Fin 3, |a j * x j| ≤ ∑ _j : Fin 3, |a 0| := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          simpa using mul_le_mul (hmax j) (hx j) (abs_nonneg _) (abs_nonneg _)
      _ = 3 * |a 0| := by simp
  have hc : |c| ≤ E + 3 * |a 0| := by
    have hid : c = (c + ∑ j, a j * w p j) - ∑ j, a j * w p j := by ring
    rw [hid]
    exact (abs_sub _ _).trans (add_le_add (hfit p hp) (hlin (w p) (hw p hp)))
  have hb := (abs_add_le c (∑ j, a j * z j)).trans (add_le_add hc (hlin z hz))
  calc |c + ∑ j, a j * z j| ≤ E + 6 * |a 0| := by linarith [hb]
    _ ≤ E + 6 * (8 * C * E / m) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hslope (by norm_num))
    _ = _ := by ring

/-- Full affine comparison without specifying the largest slope coordinate. -/
lemma affine_box_bound_of_any_mesh_witnesses {H : ℕ} (hH : 0 < H)
    (S : Finset (Fin 3 → Fin H)) (a : Fin 3 → ℝ)
    (w : (Fin 3 → Fin H) → Fin 3 → ℝ) {c E C m : ℝ}
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hm : 0 < m)
    (hmass : m ≤ C / (H : ℝ) ^ 3 * S.card) (hfine : 30 * C ≤ m * H)
    (hw : ∀ p ∈ S, ∀ j, |w p j| ≤ 1)
    (hround : ∀ p ∈ S, ∀ j, |(p j : ℕ) - (H : ℝ) * w p j| ≤ 1)
    (hfit : ∀ p ∈ S, |c + ∑ j, a j * w p j| ≤ E)
    (z : Fin 3 → ℝ) (hz : ∀ j, |z j| ≤ 1) :
    |c + ∑ j, a j * z j| ≤ E + 48 * C * E / m := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun j : Fin 3 => |a j|)
    Finset.univ_nonempty
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  let eG : (Fin 3 → Fin H) ≃ (Fin 3 → Fin H) :=
    { toFun := fun p j => p (e j)
      invFun := fun p j => p (e.symm j)
      left_inv := by intro p; funext j; simp
      right_inv := by intro p; funext j; simp }
  let S' := S.map eG.toEmbedding
  let a' : Fin 3 → ℝ := fun j => a (e j)
  let w' : (Fin 3 → Fin H) → Fin 3 → ℝ := fun p j => w (eG.symm p) (e j)
  have hcount' : m ≤ C / (H : ℝ) ^ 3 * S'.card := by simpa [S'] using hmass
  have hmax' (j : Fin 3) : |a' j| ≤ |a' 0| := by
    change |a (e j)| ≤ |a (e 0)|
    have he0 : e 0 = i := by simp [e]
    rw [he0]
    exact hi (e j) (Finset.mem_univ _)
  have hw' (p : Fin 3 → Fin H) (hp : p ∈ S') (j : Fin 3) : |w' p j| ≤ 1 := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    change |w (eG.symm (eG q)) (e j)| ≤ 1
    simpa only [Equiv.symm_apply_apply] using hw q hq (e j)
  have hround' (p : Fin 3 → Fin H) (hp : p ∈ S') (j : Fin 3) :
      |(p j : ℕ) - (H : ℝ) * w' p j| ≤ 1 := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    change |(q (e j) : ℕ) - (H : ℝ) * w (eG.symm (eG q)) (e j)| ≤ 1
    simpa only [Equiv.symm_apply_apply] using hround q hq (e j)
  have hfit' (p : Fin 3 → Fin H) (hp : p ∈ S') : |c + ∑ j, a' j * w' p j| ≤ E := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    change |c + ∑ j, a (e j) * w (eG.symm (eG q)) (e j)| ≤ E
    simp only [Equiv.symm_apply_apply]
    rw [e.sum_comp (fun j => a j * w q j)]
    exact hfit q hq
  have hb := affine_box_bound_of_mesh_witnesses hH S' a' w' hE hC hm hcount' hfine
    hmax' hw' hround' hfit' (fun j => z (e j)) (fun j => hz (e j))
  change |c + ∑ j, a (e j) * z (e j)| ≤ E + 48 * C * E / m at hb
  rw [e.sum_comp (fun j => a j * z j)] at hb
  exact hb

/-- Original-law cell ceilings and one fitted observation per occurring cell
supply the full affine comparison. No continuous density is inferred from the mesh. -/
lemma affine_box_bound_from_cell_caps {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {H : ℕ} (hH : 0 < H) (S : Finset (Fin 3 → Fin H))
    (tag : Ω → Fin 3 → Fin H) (a : Fin 3 → ℝ)
    (w : (Fin 3 → Fin H) → Fin 3 → ℝ) {c E C m : ℝ}
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hm : 0 < m)
    (hmass : ENNReal.ofReal m ≤ μ univ)
    (hcover : ∀ᵐ ω ∂μ, tag ω ∈ S)
    (hcap : ∀ p ∈ S, μ {ω | tag ω = p} ≤ ENNReal.ofReal (C / (H : ℝ) ^ 3))
    (hfine : 30 * C ≤ m * H)
    (hw : ∀ p ∈ S, ∀ j, |w p j| ≤ 1)
    (hround : ∀ p ∈ S, ∀ j, |(p j : ℕ) - (H : ℝ) * w p j| ≤ 1)
    (hfit : ∀ p ∈ S, |c + ∑ j, a j * w p j| ≤ E)
    (z : Fin 3 → ℝ) (hz : ∀ j, |z j| ≤ 1) :
    |c + ∑ j, a j * z j| ≤ E + 48 * C * E / m := by
  classical
  have hcover' : μ univ ≤ μ (⋃ p ∈ S, {ω | tag ω = p}) := by
    apply measure_mono_ae
    filter_upwards [hcover] with ω hω _
    exact mem_iUnion.mpr ⟨tag ω, mem_iUnion.mpr ⟨hω, rfl⟩⟩
  have hbound : ENNReal.ofReal m ≤ ENNReal.ofReal (C / (H : ℝ) ^ 3 * S.card) := by
    calc ENNReal.ofReal m ≤ μ univ := hmass
      _ ≤ μ (⋃ p ∈ S, {ω | tag ω = p}) := hcover'
      _ ≤ ∑ p ∈ S, μ {ω | tag ω = p} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _p ∈ S, ENNReal.ofReal (C / (H : ℝ) ^ 3) := Finset.sum_le_sum hcap
      _ = ENNReal.ofReal (C / (H : ℝ) ^ 3 * S.card) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
        simp [mul_comm]
  have hcount : m ≤ C / (H : ℝ) ^ 3 * S.card :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
  exact affine_box_bound_of_any_mesh_witnesses hH S a w hE hC hm hcount hfine
    hw hround hfit z hz


/-- An affine bound on a fitted event extends to the full box using only
finite original-law cell caps. The observations in occupied cells are chosen automatically. -/
lemma affine_box_bound_from_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {H : ℕ} (hH : 0 < H) (E₀ : Set Ω)
    (tag : Ω → Fin 3 → Fin H) (u : Ω → Fin 3 → ℝ) (a : Fin 3 → ℝ)
    {c E C m : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C) (hm : 0 < m)
    (hmass : ENNReal.ofReal m ≤ μ E₀)
    (hcap : ∀ p, μ {ω | ω ∈ E₀ ∧ tag ω = p} ≤ ENNReal.ofReal (C / (H : ℝ) ^ 3))
    (hfine : 30 * C ≤ m * H)
    (hu : ∀ ω ∈ E₀, ∀ j, |u ω j| ≤ 1)
    (hround : ∀ ω ∈ E₀, ∀ j, |(tag ω j : ℕ) - (H : ℝ) * u ω j| ≤ 1)
    (hfit : ∀ ω ∈ E₀, |c + ∑ j, a j * u ω j| ≤ E)
    (z : Fin 3 → ℝ) (hz : ∀ j, |z j| ≤ 1) :
    |c + ∑ j, a j * z j| ≤ E + 48 * C * E / m := by
  classical
  let S : Finset (Fin 3 → Fin H) := Finset.univ.filter (fun p => ∃ ω ∈ E₀, tag ω = p)
  have hex (p : Fin 3 → Fin H) (hp : p ∈ S) : ∃ ω ∈ E₀, tag ω = p :=
    (Finset.mem_filter.mp hp).2
  let w : (Fin 3 → Fin H) → Fin 3 → ℝ := fun p =>
    if hp : p ∈ S then u (Classical.choose (hex p hp)) else 0
  have hw (p : Fin 3 → Fin H) (hp : p ∈ S) (j : Fin 3) : |w p j| ≤ 1 := by
    simp only [w, dite_eq_left hp]
    exact hu _ (Classical.choose_spec (hex p hp)).1 j
  have hwr (p : Fin 3 → Fin H) (hp : p ∈ S) (j : Fin 3) :
      |(p j : ℕ) - (H : ℝ) * w p j| ≤ 1 := by
    have hw := Classical.choose_spec (hex p hp)
    simpa only [w, dite_eq_left hp, hw.2] using hround _ hw.1 j
  have hwf (p : Fin 3 → Fin H) (hp : p ∈ S) : |c + ∑ j, a j * w p j| ≤ E := by
    simpa only [w, dite_eq_left hp] using hfit _ (Classical.choose_spec (hex p hp)).1
  have hcover : E₀ ⊆ ⋃ p ∈ S, {ω | ω ∈ E₀ ∧ tag ω = p} := by
    intro ω hω
    refine mem_iUnion.mpr ⟨tag ω, mem_iUnion.mpr ⟨?_, hω, rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ω, hω, rfl⟩
  have hbound : ENNReal.ofReal m ≤ ENNReal.ofReal (C / (H : ℝ) ^ 3 * S.card) := by
    calc
      _ ≤ μ E₀ := hmass
      _ ≤ μ (⋃ p ∈ S, {ω | ω ∈ E₀ ∧ tag ω = p}) := measure_mono hcover
      _ ≤ ∑ p ∈ S, μ {ω | ω ∈ E₀ ∧ tag ω = p} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _p ∈ S, ENNReal.ofReal (C / (H : ℝ) ^ 3) := Finset.sum_le_sum (fun p _ => hcap p)
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
        simp [mul_comm]
  have hcount : m ≤ C / (H : ℝ) ^ 3 * S.card :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
  exact affine_box_bound_of_any_mesh_witnesses hH S a w hE hC hm hcount hfine
    hw hwr hwf z hz


/- The following native dual/jet kernels are promoted from our own o202
TriangularDual.lean, ContactJetNumerics.lean and NativeJetBounds.lean. -/

lemma symmetric_affine_slope_bound {A B r E : ℝ} (hr : 0 < r)
    (hp : |A + r * B| ≤ E) (hm : |A - r * B| ≤ E) : |B| ≤ E / r := by
  apply (le_div_iff₀ hr).mpr
  have hh : 2 * r * |B| ≤ 2 * E := by
    calc
      _ = |(A + r * B) - (A - r * B)| := by
        rw [show (A + r * B) - (A - r * B) = (2 * r) * B by ring,
          abs_mul, abs_of_pos (by positivity : 0 < 2 * r)]
      _ ≤ |A + r * B| + |A - r * B| := abs_sub _ _
      _ ≤ _ := by linarith
  nlinarith

/-- An affine norm bound on a triangular box controls the three dual slopes
by the inverses of the true side lengths. -/
lemma triangular_affine_dual_bounds (c g₀ g₁ g₂ t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ E : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hbound : ∀ t Z Y : ℝ, |t - t₀| ≤ r₀ →
      |Z - z₀ - l₁ * (t - t₀)| ≤ r₁ →
      |Y - y₀ - l₂ * (t - t₀) - l₃ * (Z - z₀)| ≤ r₂ →
      |c + g₀ * t + g₁ * Z + g₂ * Y| ≤ E) :
    |g₀ + l₁ * g₁ + (l₂ + l₃ * l₁) * g₂| ≤ E / r₀ ∧
    |g₁ + l₃ * g₂| ≤ E / r₁ ∧ |g₂| ≤ E / r₂ := by
  let A := c + g₀ * t₀ + g₁ * z₀ + g₂ * y₀
  let B₀ := g₀ + l₁ * g₁ + (l₂ + l₃ * l₁) * g₂
  let B₁ := g₁ + l₃ * g₂
  have htrans (u v w : ℝ) (hu : |u| ≤ r₀) (hv : |v| ≤ r₁) (hw : |w| ≤ r₂) :
      |A + u * B₀ + v * B₁ + w * g₂| ≤ E := by
    have ht : |t₀ + u - t₀| ≤ r₀ := by simpa only [add_sub_cancel_left] using hu
    have hZ : |(z₀ + l₁ * u + v) - z₀ - l₁ * ((t₀ + u) - t₀)| ≤ r₁ := by
      convert hv using 1
      congr 1
      ring
    have hY : |(y₀ + l₂ * u + l₃ * (l₁ * u + v) + w) - y₀ -
        l₂ * ((t₀ + u) - t₀) - l₃ * ((z₀ + l₁ * u + v) - z₀)| ≤ r₂ := by
      convert hw using 1
      congr 1
      ring
    convert hbound (t₀ + u) (z₀ + l₁ * u + v)
      (y₀ + l₂ * u + l₃ * (l₁ * u + v) + w) ht hZ hY using 1
    congr 1
    dsimp [A, B₀, B₁]
    ring
  have hz₀ : |(0 : ℝ)| ≤ r₀ := by simpa using hr₀.le
  have hz₁ : |(0 : ℝ)| ≤ r₁ := by simpa using hr₁.le
  have hz₂ : |(0 : ℝ)| ≤ r₂ := by simpa using hr₂.le
  have hp₀ : |r₀| ≤ r₀ := (abs_of_pos hr₀).le
  have hp₁ : |r₁| ≤ r₁ := (abs_of_pos hr₁).le
  have hp₂ : |r₂| ≤ r₂ := (abs_of_pos hr₂).le
  refine ⟨?_, ?_, ?_⟩
  · apply symmetric_affine_slope_bound hr₀ (A := A)
    · simpa only [mul_zero, zero_mul, add_zero] using htrans r₀ 0 0 hp₀ hz₁ hz₂
    · simpa only [mul_zero, zero_mul, add_zero, neg_mul, ← sub_eq_add_neg] using
        htrans (-r₀) 0 0 (by simpa only [abs_neg] using hp₀) hz₁ hz₂
  · apply symmetric_affine_slope_bound hr₁ (A := A)
    · simpa only [mul_zero, zero_mul, add_zero] using htrans 0 r₁ 0 hz₀ hp₁ hz₂
    · simpa only [mul_zero, zero_mul, add_zero, neg_mul, ← sub_eq_add_neg] using
        htrans 0 (-r₁) 0 hz₀ (by simpa only [abs_neg] using hp₁) hz₂
  · apply symmetric_affine_slope_bound hr₂ (A := A)
    · simpa only [mul_zero, zero_mul, add_zero] using htrans 0 0 r₂ hz₀ hz₁ hp₂
    · simpa only [mul_zero, zero_mul, add_zero, neg_mul, ← sub_eq_add_neg] using
        htrans 0 0 (-r₂) hz₀ hz₁ (by simpa only [abs_neg] using hp₂)

/-- Native horizontal frame alignment turns dual box slopes into a normal
coefficient bound E/q² and a tangent pair bound6*K*E/q. -/
lemma contact_frame_jet_bounds {K q g E τ Z l₁ l₂ l₃ g₀ g₁ g₂ : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (hg : 0 < g) (hE : 0 ≤ E)
    (hqg : q ≤ K * g) (hl₁ : |l₁| ≤ K)
    (hl₂ : |l₂ + Z| ≤ K * q) (hl₃ : |l₃ - τ| ≤ K * q)
    (hT : |g₀ + l₁ * g₁ + (l₂ + l₃ * l₁) * g₂| ≤ 2 * E / q)
    (hZ : |g₁ + l₃ * g₂| ≤ E / (K * q))
    (hV : |g₂| ≤ E / (K * q * g)) :
    |g₂| ≤ E / q ^ 2 ∧ |g₀ - Z * g₂| + |g₁ + τ * g₂| ≤ 6 * K * E / q := by
  have hK0 : 0 < K := by linarith
  have hA : |g₀ - Z * g₂| ≤
      2 * E / q + K * (E / (K * q)) + (K * q) * (E / (K * q * g)) := by
    calc
      _ = |(g₀ + l₁ * g₁ + (l₂ + l₃ * l₁) * g₂) -
          l₁ * (g₁ + l₃ * g₂) - (l₂ + Z) * g₂| := by congr 1; ring
      _ ≤ |g₀ + l₁ * g₁ + (l₂ + l₃ * l₁) * g₂| +
          |l₁| * |g₁ + l₃ * g₂| + |l₂ + Z| * |g₂| := by
        let T := g₀ + l₁ * g₁ + (l₂ + l₃ * l₁) * g₂
        let U := g₁ + l₃ * g₂
        have hh : |T - l₁ * U - (l₂ + Z) * g₂| ≤
            |T| + |l₁ * U| + |(l₂ + Z) * g₂| :=
          (abs_sub _ _).trans (add_le_add (abs_sub T (l₁ * U)) le_rfl)
        simpa only [T, U, abs_mul] using hh
      _ ≤ _ := add_le_add (add_le_add hT
        (mul_le_mul hl₁ hZ (abs_nonneg _) hK0.le))
        (mul_le_mul hl₂ hV (abs_nonneg _) (by positivity))
  have hB : |g₁ + τ * g₂| ≤ E / (K * q) + (K * q) * (E / (K * q * g)) := by
    calc
      _ = |(g₁ + l₃ * g₂) + (τ - l₃) * g₂| := by congr 1; ring
      _ ≤ |g₁ + l₃ * g₂| + |τ - l₃| * |g₂| := by
        simpa only [abs_mul] using (abs_add_le (g₁ + l₃ * g₂) ((τ - l₃) * g₂))
      _ ≤ _ := add_le_add hZ (mul_le_mul (by simpa only [abs_sub_comm] using hl₃)
        hV (abs_nonneg _) (by positivity))
  have hcancel₁ : K * (E / (K * q)) = E / q := by field_simp
  have hcancel₂ : (K * q) * (E / (K * q * g)) = E / g := by field_simp
  rw [hcancel₁, hcancel₂] at hA
  rw [hcancel₂] at hB
  have hdiv : E / (K * q) ≤ E / q := by
    apply (div_le_div_iff₀ (by positivity : 0 < K * q) hq).mpr
    have hh : q ≤ K * q := by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hK)]
    nlinarith [mul_le_mul_of_nonneg_left hh hE]
  have hdivg : E / g ≤ K * E / q := by
    apply (le_div_iff₀ hq).mpr
    have hh := mul_le_mul_of_nonneg_left hqg hE
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hg).mpr
    nlinarith [hh]
  have hnormal : E / (K * q * g) ≤ E / q ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < K * q * g) (sq_pos_of_pos hq)).mpr
    have hh : q ^ 2 ≤ K * q * g := by nlinarith [mul_le_mul_of_nonneg_left hqg hq.le]
    nlinarith [mul_le_mul_of_nonneg_left hh hE]
  refine ⟨hV.trans hnormal, ?_⟩
  have hEq : 0 ≤ E / q := by positivity
  have hconst : 4 + 2 * K ≤ 6 * K := by linarith
  simp only [mul_div_assoc] at hA hdivg
  calc
    _ ≤ (2 * (E / q) + E / q + E / g) + (E / (K * q) + E / g) := add_le_add hA hB
    _ ≤ 4 * (E / q) + 2 * (E / g) := by linarith [hdiv]
    _ ≤ (4 + 2 * K) * (E / q) := by nlinarith [hdivg]
    _ ≤ 6 * K * (E / q) := mul_le_mul_of_nonneg_right hconst hEq
    _ = _ := by ring

/-- The native first-jet comparison holds throughout the original box,
with the frame evaluated at the actual time and first position. -/
lemma contact_frame_jet_transport {K q E τ Z₀ l₁ g₀ g₁ g₂ t Z : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (_hE : 0 ≤ E) (hl₁ : |l₁| ≤ K)
    (ht : |t - τ| ≤ q / 2) (hZ : |Z - Z₀ - l₁ * (t - τ)| ≤ K * q)
    (hnormal : |g₂| ≤ E / q ^ 2)
    (hcenter : |g₀ - Z₀ * g₂| + |g₁ + τ * g₂| ≤ 6 * K * E / q) :
    |g₀ - Z * g₂| + |g₁ + t * g₂| ≤ 8 * K * E / q := by
  have hposition : |Z - Z₀| ≤ K * q + K * (q / 2) := by
    calc
      _ = |(Z - Z₀ - l₁ * (t - τ)) + l₁ * (t - τ)| := by congr 1; ring
      _ ≤ |Z - Z₀ - l₁ * (t - τ)| + |l₁| * |t - τ| := by
        simpa only [abs_mul] using abs_add_le (Z - Z₀ - l₁ * (t - τ)) (l₁ * (t - τ))
      _ ≤ _ := add_le_add hZ (mul_le_mul hl₁ ht (abs_nonneg _) (by linarith))
  have hcoordinates : |Z - Z₀| + |t - τ| ≤ 2 * K * q := by
    nlinarith [mul_le_mul_of_nonneg_right hK hq.le]
  have herror := mul_le_mul hcoordinates hnormal (abs_nonneg g₂) (by positivity : 0 ≤ 2 * K * q)
  have hcancel : (2 * K * q) * (E / q ^ 2) = 2 * K * E / q := by field_simp
  rw [hcancel] at herror
  have hfirst : |g₀ - Z * g₂| ≤ |g₀ - Z₀ * g₂| + |Z - Z₀| * |g₂| := by
    calc
      _ = |(g₀ - Z₀ * g₂) - (Z - Z₀) * g₂| := by congr 1; ring
      _ ≤ _ := by simpa only [abs_mul] using abs_sub (g₀ - Z₀ * g₂) ((Z - Z₀) * g₂)
  have hsecond : |g₁ + t * g₂| ≤ |g₁ + τ * g₂| + |t - τ| * |g₂| := by
    calc
      _ = |(g₁ + τ * g₂) + (t - τ) * g₂| := by congr 1; ring
      _ ≤ _ := by simpa only [abs_mul] using abs_add_le (g₁ + τ * g₂) ((t - τ) * g₂)
  simp only [mul_div_assoc] at herror hcenter ⊢
  nlinarith [hfirst, hsecond, herror, hcenter]

/-- Whole-box affine agreement gives the native horizontal normal and tangent
jet errors, with the actual true side lengths and plane alignment. -/
lemma horizontal_triangular_jet_bounds (c g₀ g₁ g₂ t₀ z₀ y₀ l₁ l₂ l₃ K q g E : ℝ)
    (hK : 1 ≤ K) (hq : 0 < q) (hg : 0 < g) (hE : 0 ≤ E)
    (hqg : q ≤ K * g) (hl₁ : |l₁| ≤ K)
    (hl₂ : |l₂ + z₀| ≤ K * q) (hl₃ : |l₃ - t₀| ≤ K * q)
    (hbound : ∀ t Z Y : ℝ, |t - t₀| ≤ q / 2 →
      |Z - z₀ - l₁ * (t - t₀)| ≤ K * q →
      |Y - y₀ - l₂ * (t - t₀) - l₃ * (Z - z₀)| ≤ K * q * g →
      |c + g₀ * t + g₁ * Z + g₂ * Y| ≤ E) :
    |g₂| ≤ E / q ^ 2 ∧ |g₀ - z₀ * g₂| + |g₁ + t₀ * g₂| ≤ 6 * K * E / q := by
  have hK0 : 0 < K := by linarith
  have hd := triangular_affine_dual_bounds c g₀ g₁ g₂ t₀ z₀ y₀ l₁ l₂ l₃
    (q / 2) (K * q) (K * q * g) E (by positivity) (by positivity) (by positivity) hbound
  have hT : |g₀ + l₁ * g₁ + (l₂ + l₃ * l₁) * g₂| ≤ 2 * E / q := by
    convert hd.1 using 1
    field_simp
  exact contact_frame_jet_bounds hK hq hg hE hqg hl₁ hl₂ hl₃ hT hd.2.1 hd.2.2

/-- The same first-jet comparison in the native frame at every point of the
original tilted box. -/
lemma horizontal_triangular_jet_bounds_at_point
    (c g₀ g₁ g₂ t₀ z₀ y₀ l₁ l₂ l₃ K q g E t Z : ℝ)
    (hK : 1 ≤ K) (hq : 0 < q) (hg : 0 < g) (hE : 0 ≤ E)
    (hqg : q ≤ K * g) (hl₁ : |l₁| ≤ K)
    (hl₂ : |l₂ + z₀| ≤ K * q) (hl₃ : |l₃ - t₀| ≤ K * q)
    (hbound : ∀ t Z Y : ℝ, |t - t₀| ≤ q / 2 →
      |Z - z₀ - l₁ * (t - t₀)| ≤ K * q →
      |Y - y₀ - l₂ * (t - t₀) - l₃ * (Z - z₀)| ≤ K * q * g →
      |c + g₀ * t + g₁ * Z + g₂ * Y| ≤ E)
    (ht : |t - t₀| ≤ q / 2)
    (hZ : |Z - z₀ - l₁ * (t - t₀)| ≤ K * q) :
    |g₂| ≤ E / q ^ 2 ∧ |g₀ - Z * g₂| + |g₁ + t * g₂| ≤ 8 * K * E / q := by
  have hb := horizontal_triangular_jet_bounds c g₀ g₁ g₂ t₀ z₀ y₀ l₁ l₂ l₃
    K q g E hK hq hg hE hqg hl₁ hl₂ hl₃ hbound
  exact ⟨hb.1, contact_frame_jet_transport hK hq hE hl₁ ht hZ hb.1 hb.2⟩

end Submission.Lib.K4AffineMesh
