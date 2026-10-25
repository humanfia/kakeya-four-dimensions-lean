-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.CellsQ.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Assembly
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatExitQ
-- Copied from session x0338 (o070 branch, commit ec01e52, file X305/CellsQ.lean), namespace renamed.

/-!
# Cells to flat prisms with the quadratic count

`cell_cover_sep` is x0305's `cell_cover` (proof copied) also exporting the separation
`NetSeparated ρ z w` of the net it builds; `flat_exit_of_cells_q` is x0305's
`flat_exit_of_cells` (proof copied) through `cell_cover_sep` and `flat_exit_q`, so its output
prisms also satisfy the global quadratic count (`FlatPrismsQ`).
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

open MeasureTheory

/-- `cell_cover`, also exporting the separation `NetSeparated ρ z w` of the net. -/
theorem cell_cover_sep {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : 2 * δ ≤ ρ) (hρ : ρ ≤ 1 / 10000)
    {n : ℕ} (x v : Fin n → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : ∀ i, x i = leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (hcls : ∀ i ∈ S, ∀ i' ∈ S, classKey 200000 ρ (x i) (v i) = classKey 200000 ρ (x i') (v i')) :
    ∃ q : ℕ, 0 < q ∧ ∃ z w : Fin q → Sp, (∀ j, ‖w j‖ = 1) ∧
      (∀ j j', j ≠ j' → MeasureTheory.volume
          (Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ∩
            Metric.thickening ρ (segment ℝ (z j') (z j' + w j'))) ≤
          (1 / 2 : ENNReal) *
            MeasureTheory.volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)))) ∧
      (∀ i ∈ S, ∃! j, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧
      (∀ j, ∃ i ∈ S, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧
      (∀ j, ∃ i₀ ∈ S, z j = x i₀ ∧ w j = v i₀ ∧
          ∀ i ∈ S, (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ↔
            lineCell (ρ / 20) (x i) (v i) = lineCell (ρ / 20) (x i₀) (v i₀))) ∧
      NetSeparated ρ z w := by
  classical
  have hρ0 : 0 < ρ := by linarith
  set s : ℝ := ρ / 20 with hsdef
  have hs : 0 < s := by positivity
  set C := S.image (fun i => lineCell s (x i) (v i)) with hCdef
  have hrep : ∀ κ ∈ C, ∃ i ∈ S, lineCell s (x i) (v i) = κ := fun κ hκ => by
    simpa [hCdef] using hκ
  let rep : C → Fin n := fun κ => (hrep κ.1 κ.2).choose
  have hrepS : ∀ κ : C, rep κ ∈ S := fun κ => (hrep κ.1 κ.2).choose_spec.1
  have hrepcell : ∀ κ : C, lineCell s (x (rep κ)) (v (rep κ)) = κ.1 :=
    fun κ => (hrep κ.1 κ.2).choose_spec.2
  let e : C ≃ Fin C.card := C.equivFin
  have hCpos : 0 < C.card := by
    rw [Finset.card_pos]; exact hS.image _
  set z : Fin C.card → Sp := fun j => x (rep (e.symm j)) with hzdef
  set w : Fin C.card → Sp := fun j => v (rep (e.symm j)) with hwdef
  -- separation of the net
  have hsep : NetSeparated ρ z w := by
    intro j j' hjj'
    have hne : lineCell s (x (rep (e.symm j))) (v (rep (e.symm j))) ≠
        lineCell s (x (rep (e.symm j'))) (v (rep (e.symm j'))) := by
      rw [hrepcell, hrepcell]
      intro h
      exact hjj' (e.symm.injective (Subtype.ext h))
    have hkey := hcls _ (hrepS (e.symm j)) _ (hrepS (e.symm j'))
    have hc1 : ∀ c, (lineCell s (x (rep (e.symm j))) (v (rep (e.symm j)))).1 c % ((200000 : ℕ) : ℤ) =
        (lineCell s (x (rep (e.symm j'))) (v (rep (e.symm j')))).1 c % ((200000 : ℕ) : ℤ) :=
      fun c => congrFun (congrArg Prod.fst hkey) c
    have hc2 : ∀ c, (lineCell s (x (rep (e.symm j))) (v (rep (e.symm j)))).2 c % ((200000 : ℕ) : ℤ) =
        (lineCell s (x (rep (e.symm j'))) (v (rep (e.symm j')))).2 c % ((200000 : ℕ) : ℤ) :=
      fun c => congrFun (congrArg Prod.snd hkey) c
    exact separated_of_same_class hδ hρ0 hρ (le_refl _) (hv _) (hv _) (hT _) (hT _)
      (hcan _) (hcan _) (hanti _ _) hc1 hc2 hne
  -- containment in the net tube of the own cell
  let own : ∀ i, i ∈ S → Fin C.card := fun i hi =>
    e ⟨_, Finset.mem_image_of_mem (fun i => lineCell s (x i) (v i)) hi⟩
  have hown : ∀ i (hi : i ∈ S), Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.thickening ρ (segment ℝ (z (own i hi)) (z (own i hi) + w (own i hi))) := by
    intro i hi
    simp only [hzdef, hwdef, own, Equiv.symm_apply_apply]
    apply subset_of_same_cell hδ hs (by rw [hsdef]; linarith) (hv i) (hv _) (hT i) (hT _)
      (hcan i) (hcan _)
    rw [hrepcell]
  -- uniqueness
  have huniq : ∀ i ∈ S, ∀ j j₀, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.thickening ρ (segment ℝ (z j) (z j + w j)) →
      Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.thickening ρ (segment ℝ (z j₀) (z j₀ + w j₀)) → j = j₀ := by
    intro i hi j j₀ hj hj₀
    by_contra hne
    rcases hsep j j₀ hne with htr | hfar
    · have h1 := direction_near_of_subset hδ (hv i) (hv _) hj
      have h2 := direction_near_of_subset hδ (hv i) (hv _) hj₀
      have := min_dir_triangle (v := v i) (w := w j) (w' := w j₀)
      linarith
    · obtain ⟨⟨θ1, h01, h11, hd1⟩, -⟩ := endpoints_near_of_subset hδ hj
      obtain ⟨⟨θ2, h02, h12, hd2⟩, -⟩ := endpoints_near_of_subset hδ hj₀
      have := hfar (z j + θ1 • w j) (mem_segment_add_iff.2 ⟨θ1, h01, h11, rfl⟩)
        (z j₀ + θ2 • w j₀) (mem_segment_add_iff.2 ⟨θ2, h02, h12, rfl⟩)
      have := dist_triangle_left (z j + θ1 • w j) (z j₀ + θ2 • w j₀) (x i)
      linarith
  refine ⟨C.card, hCpos, z, w, fun j => hv _, fun j j' hjj' => ?_, fun i hi => ?_,
    fun j => ?_, fun j => ?_, hsep⟩
  · rcases hsep j j' hjj' with htr | hfar
    · exact half_overlap_of_transverse hρ0 (by linarith) (hv _) (hv _) htr
    · exact half_overlap_of_far hfar
  · exact ⟨_, hown i hi, fun j hj => huniq i hi j _ hj (hown i hi)⟩
  · refine ⟨rep (e.symm j), hrepS _, ?_⟩
    exact Metric.thickening_mono (by linarith) _
  · refine ⟨rep (e.symm j), hrepS _, rfl, rfl, fun i hi => ⟨fun hsub => ?_, fun hcell => ?_⟩⟩
    · -- inside the net tube `j` means: `j` is the own net tube, i.e. the same cell
      have hjj := huniq i hi j _ hsub (hown i hi)
      have : e.symm j = ⟨_, Finset.mem_image_of_mem (fun i => lineCell s (x i) (v i)) hi⟩ := by
        rw [hjj]; simp only [own, Equiv.symm_apply_apply]
      rw [hrepcell (e.symm j), this]
    · simp only [hzdef, hwdef]
      apply subset_of_same_cell hδ hs (by rw [hsdef]; linarith) (hv i) (hv _) (hT i) (hT _)
        (hcan i) (hcan _)
      exact hcell

open Classical in
/-- `flat_exit_of_cells` with the quadratic count (through `flat_exit_q`; extra error bound
`herrorQ`).  The flat exit from whole flat cells at one level. `B` is a union of whole cells (radius `ρ`)
of a canonical set `S` with a common class; each cell of `B` carries fibre_dichotomy's FLAT
certificate. Then x0318's `flat_exit` gives frozen SC for a subfamily of `B` of size at least
`δ^θ |B|`. -/
theorem flat_exit_of_cells_q {δ ρ ν Λ ζ ζ₂ ζ₃ θ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν)
    (hζ : 0 ≤ ζ) (hζ₂ : 0 ≤ ζ₂) (hδρ : 2 * δ ≤ ρ) (hρ : ρ ≤ 1 / 10000)
    (hΛ : 16 * δ ^ (-ν - ζ₂ / 200) ≤ Λ) (h64 : 64 * δ ^ ν ≤ 1)
    (herror : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.localFlatLoss * δ ^ (ζ₃ - ζ - 5 * (2 * ν)) ≤ 1)
    (hretain : 2 * δ ^ (θ - 2 * ν) ≤ 1)
    (herrorQ : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.quadLoss *
      δ ^ (ζ₃ - 8 * (2 * ν)) ≤ 1)
    {m : ℕ} (x v : Fin m → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : ∀ i, x i = leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (S : Finset (Fin m)) (hS : S.Nonempty)
    (hcls : ∀ i ∈ S, ∀ i' ∈ S, classKey 200000 ρ (x i) (v i) = classKey 200000 ρ (x i') (v i'))
    (B : Finset (Fin m)) (hBS : B ⊆ S) (hBne : B.Nonempty)
    (hwhole : ∀ i ∈ B, ∀ j ∈ S, lineCell (ρ / 20) (x j) (v j) = lineCell (ρ / 20) (x i) (v i) →
      j ∈ B)
    (hcert : ∀ i ∈ B, ∃ a b : ℝ, δ ≤ a ∧ Λ * a < b ∧ b ≤ 2 ∧
      WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LongFactor ν δ a b (fun j : Fin (fibre S (fun i => lineCell (ρ / 20) (x i) (v i)) i).card =>
        Metric.thickening δ (segment ℝ
          (x ((fibre S (fun i => lineCell (ρ / 20) (x i) (v i)) i).equivFin.symm j))
          (x ((fibre S (fun i => lineCell (ρ / 20) (x i) (v i)) i).equivFin.symm j) +
            v ((fibre S (fun i => lineCell (ρ / 20) (x i) (v i)) i).equivFin.symm j)))))
    (hFB : ∀ W : Set Sp, Convex ℝ W →
      ENNReal.ofReal ((B.filter (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card : ℝ) ≤
        ENNReal.ofReal (δ ^ (-ζ) * B.card) * volume W)
    (hpig : (((Nat.log 2 ⌊2 / δ⌋₊ + 1) * (Nat.log 2 ⌊2 / δ⌋₊ + 1) *
        (Nat.log 2 ⌊(B.card : ℝ) * δ ^ (-ν)⌋₊ + 1) : ℕ) : ℝ) ≤ δ ^ (-ν)) :
    ∃ (k : ℕ) (g : Fin k → Fin m), Function.Injective g ∧ (∀ j, g j ∈ B) ∧
      δ ^ θ * B.card ≤ k ∧
      WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatPrismsQ ζ₂ ζ₃ δ (fun j => Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j)))) := by
  classical
  set κ : Fin m → (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun i => lineCell (ρ / 20) (x i) (v i) with hκdef
  -- the parents: the exact cover of `S` at radius `ρ`
  obtain ⟨q, -, z, w, hw, hov, hexu, -, hfib, hnet⟩ :=
    cell_cover_sep hδ hδρ hρ x v hv hT hcan hanti S hS hcls
  -- the family of `B`
  set nB := B.card with hnB
  let eB : Fin nB ≃ B := B.equivFin.symm
  set xB : Fin nB → Sp := fun j => x (eB j) with hxB
  set vB : Fin nB → Sp := fun j => v (eB j) with hvB
  have heBS : ∀ j, (eB j : Fin m) ∈ S := fun j => hBS (eB j).2
  let par : Fin nB → Fin q := fun j => (hexu (eB j) (heBS j)).choose
  have hpar : ∀ j, Metric.thickening δ (segment ℝ (xB j) (xB j + vB j)) ⊆
      Metric.thickening ρ (segment ℝ (z (par j)) (z (par j) + w (par j))) :=
    fun j => (hexu (eB j) (heBS j)).choose_spec.1
  have huniq : ∀ j l, Metric.thickening δ (segment ℝ (xB j) (xB j + vB j)) ⊆
      Metric.thickening ρ (segment ℝ (z l) (z l + w l)) → l = par j :=
    fun j l h => (hexu (eB j) (heBS j)).choose_spec.2 l h
  have hnBpos : 0 < nB := Finset.card_pos.2 hBne
  -- Frostman of the `B`-family
  have hFrostB : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Frostman (δ ^ (-ζ)) (fun j => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Tube δ (xB j) (vB j)) := by
    intro W hW
    have hcnt : Set.ncard {j : Fin nB | WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Tube δ (xB j) (vB j) ⊆ W} =
        (B.filter (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card :=
      ncard_enum B (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)
    rw [hcnt]
    exact hFB W hW
  -- the FLAT certificates of the parents' fibres
  have hflat : ∀ l, (Finset.univ.filter (fun j => par j = l)).Nonempty → ∃ a b : ℝ,
      δ ≤ a ∧ Λ * a < b ∧ b ≤ 2 ∧
      WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LongFactor ν δ a b (fun j : Fin (Finset.univ.filter (fun j => par j = l)).card =>
        WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Tube δ (xB ((Finset.univ.filter (fun j => par j = l)).equivFin.symm j))
          (vB ((Finset.univ.filter (fun j => par j = l)).equivFin.symm j))) := by
    intro l hl
    obtain ⟨j₀, hj₀⟩ := hl
    have hj₀l : par j₀ = l := (Finset.mem_filter.1 hj₀).2
    set i₀ : Fin m := (eB j₀).1 with hi₀
    have hi₀B : i₀ ∈ B := (eB j₀).2
    obtain ⟨a, b, hδa, hab, hb2, hLF⟩ := hcert i₀ hi₀B
    refine ⟨a, b, hδa, hab, hb2, ?_⟩
    set P := Finset.univ.filter (fun j => par j = l) with hP
    set F := fibre S κ i₀ with hF
    -- `par j = l` iff the tube of `eB j` is in the cell of `i₀`
    obtain ⟨i₁, hi₁, -, -, hiff⟩ := hfib l
    have hpar_iff : ∀ j, par j = l ↔ κ (eB j) = κ i₀ := by
      intro j
      have h0 : κ i₀ = κ i₁ := by
        have := (hiff i₀ (hBS hi₀B)).1 (hj₀l ▸ hpar j₀)
        exact this
      constructor
      · intro hjl
        have := (hiff (eB j) (heBS j)).1 (hjl ▸ hpar j)
        exact this.trans h0.symm
      · intro hc
        have hsub : Metric.thickening δ (segment ℝ (xB j) (xB j + vB j)) ⊆
            Metric.thickening ρ (segment ℝ (z l) (z l + w l)) :=
          (hiff (eB j) (heBS j)).2 (hc.trans h0)
        exact (huniq j l hsub).symm
    -- the map `P → F`
    have hmemF : ∀ t : Fin P.card, (eB (P.equivFin.symm t) : Fin m) ∈ F := by
      intro t
      have ht := (P.equivFin.symm t).2
      have hpl : par (P.equivFin.symm t) = l := (Finset.mem_filter.1 ht).2
      exact Finset.mem_filter.2 ⟨heBS _, (hpar_iff _).1 hpl⟩
    let φ : Fin P.card → Fin F.card := fun t => F.equivFin ⟨eB (P.equivFin.symm t), hmemF t⟩
    have hφinj : Function.Injective φ := by
      intro t t' h
      have h1 := F.equivFin.injective h
      have h2 : (eB (P.equivFin.symm t)).1 = (eB (P.equivFin.symm t')).1 := by
        have := congrArg (fun z : {i // i ∈ F} => z.1) h1
        exact this
      have h3 : eB (P.equivFin.symm t) = eB (P.equivFin.symm t') := Subtype.ext h2
      have h4 : ((P.equivFin.symm t : Fin nB)) = (P.equivFin.symm t' : Fin nB) := eB.injective h3
      exact P.equivFin.symm.injective (Subtype.ext h4)
    have hφsurj : Function.Surjective φ := by
      intro u
      set f := F.equivFin.symm u with hf
      have hfF : (f : Fin m) ∈ F := f.2
      obtain ⟨hfS, hfc⟩ := Finset.mem_filter.1 hfF
      have hfB : (f : Fin m) ∈ B := hwhole i₀ hi₀B f hfS hfc
      set j := eB.symm ⟨f, hfB⟩ with hj
      have hjP : j ∈ P := by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (hpar_iff j).2 ?_⟩
        simp only [hj, Equiv.apply_symm_apply]
        exact hfc
      refine ⟨P.equivFin ⟨j, hjP⟩, ?_⟩
      have e3 : (⟨(eB (P.equivFin.symm (P.equivFin ⟨j, hjP⟩)) : Fin m),
          hmemF (P.equivFin ⟨j, hjP⟩)⟩ : F) = f := by
        apply Subtype.ext
        simp only [Equiv.symm_apply_apply, hj, Equiv.apply_symm_apply]
      calc φ (P.equivFin ⟨j, hjP⟩) = F.equivFin f := congrArg F.equivFin e3
        _ = u := by rw [hf, Equiv.apply_symm_apply]
    let σ : Fin P.card ≃ Fin F.card := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
    have hre := longFactor_reindex _ σ hLF
    have hfun : (fun j : Fin P.card => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Tube δ (xB (P.equivFin.symm j)) (vB (P.equivFin.symm j))) =
        (fun j => Metric.thickening δ (segment ℝ (x ↑(F.equivFin.symm (σ j)))
          (x ↑(F.equivFin.symm (σ j)) + v ↑(F.equivFin.symm (σ j))))) := by
      funext j
      have hσj : F.equivFin.symm (σ j) = ⟨eB (P.equivFin.symm j), hmemF j⟩ := by
        show F.equivFin.symm (φ j) = _
        simp only [φ, Equiv.symm_apply_apply]
      rw [hσj]
      rfl
    rw [hfun]
    exact hre
  -- apply `flat_exit`
  have hρ8 : ρ ≤ 1 / 8 := by linarith
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨k, g', hg', hk, hFP⟩ := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.flat_exit_q hδ hδ1 hν hζ hζ₂ hρ0 hρ8 hΛ h64 hnBpos hpig
    herror hretain xB vB (fun j => hv _) (fun j => hT _) hFrostB z w hw hov hnet (by linarith) herrorQ par hpar huniq hflat
  refine ⟨k, fun j => eB (g' j), fun j j' h => hg' (eB.injective (Subtype.ext h)),
    fun j => (eB (g' j)).2, hk, hFP⟩

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
