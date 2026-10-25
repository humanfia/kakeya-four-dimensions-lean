-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.Wrap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.Main
import Submission.WZ.Obl.wz_essentially_distinct_tube_count

/-!
# The frozen single-tube grains statement

The fibre `F ⊆ Fin n` is reindexed by `Fin F.card`; the essential distinctness `X` bounds
`#F` through the accepted `wz_essentially_distinct_tube_count` (after translating the coarse
tube to the origin); the cardinality part is x0448's Córdoba count
(`X48.exists_broad_card_parameters`).
-/

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_tube_grains

open Set Metric MeasureTheory
open scoped Classical

local notation "V" => LeanEval.Analysis.WangZahlKakeya.Space

/-- The coarse tube lies in the unit ball around its centre. -/
theorem coarse_tube_subset_ball {ρ : ℝ} (hρ1 : ρ ≤ 1) {y w : V} (hw : ‖w‖ = 1) :
    Tb (ρ / 2) y w ⊆ Metric.ball (y + (1 / 2 : ℝ) • w) 1 := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  rw [Metric.mem_ball]
  have h1 : dist (y + s • w) (y + (1 / 2 : ℝ) • w) ≤ 1 / 2 := by
    rw [dist_eq_norm, show y + s • w - (y + (1 / 2 : ℝ) • w) = (s - 1 / 2) • w by module,
      norm_smul, hw, mul_one, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h2 := dist_triangle p (y + s • w) (y + (1 / 2 : ℝ) • w)
  linarith

/-- The number of essentially distinct unit `δ`-tubes in a coarse tube is at most `C δ⁻⁶`. -/
theorem fibre_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 / 100 → ρ ≤ 1 →
      ∀ (m : ℕ) (x v : Fin m → V) (y w : V), ‖w‖ = 1 →
      (∀ j, ‖v j‖ = 1 ∧ Tb δ (x j) (v j) ⊆ Tb (ρ / 2) y w) →
      (∀ j k, j ≠ k → volume (Tb δ (x j) (v j) ∩ Tb δ (x k) (v k)) ≤
        1 / 2 * volume (Tb δ (x j) (v j))) →
      (m : ℝ) * δ ^ 6 ≤ C := by
  obtain ⟨C, hC, hcount⟩ := WangZahlLot.wz_essentially_distinct_tube_count
  refine ⟨C, hC, ?_⟩
  intro δ ρ hδ hδ1 hρ1 m x v y w hw hT hX
  set c₀ : V := y + (1 / 2 : ℝ) • w
  have htr : ∀ j, Tb δ (x j + -c₀) (v j) = (fun p : V => p + -c₀) '' Tb δ (x j) (v j) :=
    fun j => wz_nsp_translation_model.tube_translate δ (x j) (v j) (-c₀)
  have hinj : Function.Injective (fun p : V => p + -c₀) := fun a b h => add_right_cancel h
  apply hcount δ hδ hδ1 m (fun j => x j + -c₀) v (fun j => (hT j).1)
  · intro j
    exact RIS.translated_tube_in_unit_ball ((hT j).2.trans (coarse_tube_subset_ball hρ1 hw))
  · intro j k hjk
    have h := hX j k hjk
    show volume (Tb δ (x j + -c₀) (v j) ∩ Tb δ (x k + -c₀) (v k)) ≤
      1 / 2 * volume (Tb δ (x j + -c₀) (v j))
    rw [htr j, htr k, ← Set.image_inter hinj, RIS.volume_image_translation,
      RIS.volume_image_translation]
    exact h

end WangZahlLot.Obl.wz_coarse_tube_grains

namespace WangZahlLot.Obl.wz_coarse_tube_grains

open scoped Classical

set_option maxHeartbeats 1600000 in
/-- The single-tube grains theorem in its frozen form (`TubeGrains` of o151's split). -/
theorem tube_grains_frozen : (∀β τ ε:ℝ,0<β→0<τ→0<ε→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ ENNReal)(ι:V→ Fin 3→ℝ)(M:Set V→ Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀P,P=(fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})→∃η d₀:ℝ,0<η∧0<d₀∧∀δ ρ:ℝ,0<δ→δ≤d₀→δ≤ρ→ρ≤1→∀(n:ℕ)(x v:Fin n→ V)(Z:Fin n→ Set V)(F:Finset (Fin n))(y w:V),F.Nonempty→‖w‖=1→(∀i∈F,‖v i‖=1∧T δ (x i) (v i)⊆T (ρ/2) y w∧M (Z i)∧Z i⊆T δ (x i) (v i))→(∀i,i∉F→ Z i=∅)→X δ n x v→ O (δ^η*F.card*δ^2)≤∑i∈F,μ (Z i)→(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-η)*(r/ρ)^β*q n {i|p∈Z i})→4*δ^ε*(ρ/δ)≤(F.card:ℝ)∧∀c:ℝ,δ^(1-τ)/ρ≤c→ c≤δ^ε*(ρ/δ)/F.card→∃(Z':Fin n→ Set V)(m:ℝ)(L:ℕ)(z:Fin L→ V)(e:Fin L→ V≃ₗᵢ[ℝ]V)(G:Fin L→ Set V),(∀i,M (Z' i)∧Z' i⊆Z i)∧O (δ^ε)*∑i∈F,μ (Z i)≤∑i∈F,μ (Z' i)∧(∀(p u:V)(r:ℝ),‖u‖=1→δ≤r→ r≤ρ→ q n {i|p∈Z' i∧min ‖v i-u‖ ‖v i+u‖≤r}≤δ^(-ε)*(r/ρ)^β*q n {i|p∈Z' i})∧(∀p,(∃i,p∈Z' i)→ q n {i|p∈Z' i}∈Set.Icc m (2*m))∧(fun(U:Fin L→ Set V)=>(∀j,M (G j)∧G j⊆U j∧U j⊆T ρ y w∧ι (e j w) 0^2+ι (e j w) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→ Disjoint (G j) (G j'))∧{p|∃j,p∈G j}={p|∃i,p∈Z' i}∧O (δ^ε*L*(16*δ)*(ρ*c)*c)≤∑j,μ (G j)∧∀i j,(Z' i∩G j).Nonempty→ Z' i∩U j⊆G j∧(∀p∈T δ (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T δ (x i) (v i)∩U j,ι (e j (p-z j)) 2=t) (fun j=>P (16*δ) (ρ*c) c (z j) (e j))) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet) := by
  intro β τ ε hβ hτ hε
  intro O hO q hq T hT X hX P hP
  subst hO hq hT hX hP
  obtain ⟨C₀, hC₀, hcount⟩ := fibre_count_bound
  obtain ⟨η₁, d₁, hη₁, -, hd₁, -, hcard⟩ := X48.exists_broad_card_parameters β ε hβ hε
  obtain ⟨η₂, d₂, hη₂, hd₂, hmain⟩ := tube_grains_fin (C₀ := C₀) hβ hτ hε hC₀
  refine ⟨min η₁ η₂, min (min d₁ d₂) (1 / 100), lt_min hη₁ hη₂, by positivity, ?_⟩
  intro δ ρ hδ hδd hδρ hρ1 n x v Z F y w hF hw hZF hZoff hXd hdens hbroad
  simp only [le_min_iff] at hδd
  obtain ⟨⟨hδ1, hδ2⟩, hδ100⟩ := hδd
  have hδle1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hρ : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hpow₁ : δ ^ η₁ ≤ δ ^ (min η₁ η₂) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδle1 (min_le_left _ _)
  have hpow₂ : δ ^ η₂ ≤ δ ^ (min η₁ η₂) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδle1 (min_le_right _ _)
  have hnpow₁ : δ ^ (-(min η₁ η₂)) ≤ δ ^ (-η₁) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδle1 (by linarith [min_le_left η₁ η₂])
  have hnpow₂ : δ ^ (-(min η₁ η₂)) ≤ δ ^ (-η₂) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδle1 (by linarith [min_le_right η₁ η₂])
  have hmemF : ∀ i p, p ∈ Z i → i ∈ F := by
    intro i p hp
    by_contra hi
    rw [hZoff i hi] at hp
    exact hp
  have hbroad' : ∀ (l : ℝ), δ ^ (-(min η₁ η₂)) ≤ l → ∀ (p u : LeanEval.Analysis.WangZahlKakeya.Space) (r : ℝ), ‖u‖ = 1 → δ ≤ r →
      r ≤ ρ → (({i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} : Set (Fin n)).ncard : ℝ) ≤
        l * (r / ρ) ^ β * (({i | p ∈ Z i} : Set (Fin n)).ncard : ℝ) := by
    intro l hl p u r hu hr hrρ
    have h : (({i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} : Set (Fin n)).ncard : ℝ) ≤
        δ ^ (-(min η₁ η₂)) * (r / ρ) ^ β * (({i | p ∈ Z i} : Set (Fin n)).ncard : ℝ) :=
      hbroad p u r hu hr hrρ
    have h0 : 0 ≤ (r / ρ) ^ β * (({i | p ∈ Z i} : Set (Fin n)).ncard : ℝ) :=
      mul_nonneg (Real.rpow_nonneg (div_nonneg (hδ.le.trans hr) hρ.le) _) (Nat.cast_nonneg _)
    calc (({i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} : Set (Fin n)).ncard : ℝ)
        ≤ δ ^ (-(min η₁ η₂)) * ((r / ρ) ^ β * (({i | p ∈ Z i} : Set (Fin n)).ncard : ℝ)) := by
          rw [← mul_assoc]; exact h
      _ ≤ l * ((r / ρ) ^ β * (({i | p ∈ Z i} : Set (Fin n)).ncard : ℝ)) :=
          mul_le_mul_of_nonneg_right hl h0
      _ = l * (r / ρ) ^ β * (({i | p ∈ Z i} : Set (Fin n)).ncard : ℝ) := by ring
  refine ⟨?_, ?_⟩
  · -- the cardinality of the fibre
    apply hcard δ ρ hδ hδ1 hδρ hρ1 n x v Z F hF (fun i hi => (hZF i hi).1)
      (fun i hi => (hZF i hi).2.2.2)
    · exact le_trans (ENNReal.ofReal_le_ofReal (by gcongr)) hdens
    · intro p u r hu hr hrρ
      have e1 : ({i | i ∈ F ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} : Set (Fin n)) =
          {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} := by
        ext i
        exact ⟨fun h => h.2, fun h => ⟨hmemF i p h.1, h⟩⟩
      have e2 : ({i | i ∈ F ∧ p ∈ Z i} : Set (Fin n)) = {i | p ∈ Z i} := by
        ext i
        exact ⟨fun h => h.2, fun h => ⟨hmemF i p h, h⟩⟩
      show (({i | i ∈ F ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} : Set (Fin n)).ncard : ℝ) ≤
        δ ^ (-η₁) * (r / ρ) ^ β * (({i | i ∈ F ∧ p ∈ Z i} : Set (Fin n)).ncard : ℝ)
      rw [e1, e2]
      exact hbroad' (δ ^ (-η₁)) hnpow₁ p u r hu hr hrρ
  · -- the grains, after reindexing the fibre
    intro c hc1 hc2
    set m := F.card with hm_def
    have hm : 0 < m := Finset.card_pos.mpr hF
    set σ : Fin m → Fin n := fun j => (F.equivFin.symm j : Fin n) with hσ_def
    have hσF : ∀ j, σ j ∈ F := fun j => (F.equivFin.symm j).2
    have hσinj : Function.Injective σ := fun a b h =>
      F.equivFin.symm.injective (Subtype.ext h)
    have hσidx : ∀ i (hi : i ∈ F), σ (F.equivFin ⟨i, hi⟩) = i := by
      intro i hi
      simp [hσ_def]
    have hidxσ : ∀ j, F.equivFin ⟨σ j, hσF j⟩ = j := by
      intro j
      simp [hσ_def]
    have hsum : ∀ f : Fin n → ENNReal, ∑ i ∈ F, f i = ∑ j : Fin m, f (σ j) := by
      intro f
      rw [← Finset.sum_coe_sort F f]
      exact (Equiv.sum_comp F.equivFin.symm (fun i : F => f i)).symm
    have hncard : ∀ R : Fin n → Prop, (∀ i, R i → i ∈ F) →
        (({i | R i} : Set (Fin n)).ncard : ℝ) = (({j | R (σ j)} : Set (Fin m)).ncard : ℝ) := by
      intro R hR
      have himg : ({i | R i} : Set (Fin n)) = σ '' {j | R (σ j)} := by
        ext i
        constructor
        · intro hi
          have hiF := hR i hi
          refine ⟨F.equivFin ⟨i, hiF⟩, ?_, hσidx i hiF⟩
          show R (σ (F.equivFin ⟨i, hiF⟩))
          rw [hσidx i hiF]
          exact hi
        · rintro ⟨j, hj, rfl⟩
          exact hj
      rw [himg, Set.ncard_image_of_injective _ hσinj]
    have hZ' : ∀ j, ‖v (σ j)‖ = 1 ∧ Tb δ (x (σ j)) (v (σ j)) ⊆ Tb (ρ / 2) y w ∧
        MeasurableSet (Z (σ j)) ∧ Z (σ j) ⊆ Tb δ (x (σ j)) (v (σ j)) :=
      fun j => hZF (σ j) (hσF j)
    have hcnt : (m : ℝ) * δ ^ 6 ≤ C₀ :=
      hcount δ ρ hδ hδ100 hρ1 m (fun j => x (σ j)) (fun j => v (σ j)) y w hw
        (fun j => ⟨(hZ' j).1, (hZ' j).2.1⟩) (fun j k hjk => hXd (σ j) (σ k) (hσinj.ne hjk))
    have hdens' : ENNReal.ofReal (δ ^ η₂ * m * δ ^ 2) ≤ ∑ j, MeasureTheory.volume (Z (σ j)) := by
      rw [← hsum (fun i => MeasureTheory.volume (Z i))]
      exact le_trans (ENNReal.ofReal_le_ofReal (by gcongr)) hdens
    have hbroadm : ∀ (p u : LeanEval.Analysis.WangZahlKakeya.Space) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
        (({j | p ∈ Z (σ j) ∧ min ‖v (σ j) - u‖ ‖v (σ j) + u‖ ≤ r} : Set (Fin m)).ncard : ℝ) ≤
          δ ^ (-η₂) * (r / ρ) ^ β * (({j | p ∈ Z (σ j)} : Set (Fin m)).ncard : ℝ) := by
      intro p u r hu hr hrρ
      rw [← hncard (fun i => p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r)
        (fun i h => hmemF i p h.1), ← hncard (fun i => p ∈ Z i) (fun i h => hmemF i p h)]
      exact hbroad' (δ ^ (-η₂)) hnpow₂ p u r hu hr hrρ
    obtain ⟨Zm, mm, L, z, e, G, hZm, hret, hbr, hmult, hboxes, hdisj, hunion, hdensG, hcross⟩ :=
      hmain δ ρ hδ hδ2 hδρ hρ1 m (fun j => x (σ j)) (fun j => v (σ j)) (fun j => Z (σ j)) y w hm
        hw hZ' hcnt hdens' hbroadm c hc1 hc2
    set Zn : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space := fun i => if h : i ∈ F then Zm (F.equivFin ⟨i, h⟩) else ∅
      with hZn_def
    have hZnσ : ∀ j, Zn (σ j) = Zm j := by
      intro j
      simp only [hZn_def, dif_pos (hσF j), hidxσ j]
    have hZnoff : ∀ i, i ∉ F → Zn i = ∅ := fun i hi => by simp only [hZn_def, dif_neg hi]
    have hZnF : ∀ i p, p ∈ Zn i → i ∈ F := by
      intro i p hp
      by_contra hi
      rw [hZnoff i hi] at hp
      exact hp
    have hZnidx : ∀ i (hi : i ∈ F), Zn i = Zm (F.equivFin ⟨i, hi⟩) := by
      intro i hi
      simp only [hZn_def, dif_pos hi]
    refine ⟨Zn, mm, L, z, e, G, ?_, ?_, ?_, ?_, hboxes, hdisj, ?_, hdensG, ?_⟩
    · intro i
      by_cases hi : i ∈ F
      · rw [hZnidx i hi]
        refine ⟨(hZm _).1, (hZm _).2.trans ?_⟩
        show Z (σ (F.equivFin ⟨i, hi⟩)) ⊆ Z i
        rw [hσidx i hi]
      · rw [hZnoff i hi]
        exact ⟨MeasurableSet.empty, Set.empty_subset _⟩
    · rw [hsum (fun i => MeasureTheory.volume (Z i)), hsum (fun i => MeasureTheory.volume (Zn i))]
      simp only [hZnσ]
      exact hret
    · intro p u r hu hr hrρ
      show (({i | p ∈ Zn i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} : Set (Fin n)).ncard : ℝ) ≤
        δ ^ (-ε) * (r / ρ) ^ β * (({i | p ∈ Zn i} : Set (Fin n)).ncard : ℝ)
      rw [hncard (fun i => p ∈ Zn i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r) (fun i h => hZnF i p h.1),
        hncard (fun i => p ∈ Zn i) (fun i h => hZnF i p h)]
      simp only [hZnσ]
      exact hbr p u r hu hr hrρ
    · intro p hp
      obtain ⟨i, hi⟩ := hp
      have hiF := hZnF i p hi
      show (({i | p ∈ Zn i} : Set (Fin n)).ncard : ℝ) ∈ Set.Icc mm (2 * mm)
      rw [hncard (fun i => p ∈ Zn i) (fun i h => hZnF i p h)]
      simp only [hZnσ]
      refine hmult p ⟨F.equivFin ⟨i, hiF⟩, ?_⟩
      rw [← hZnidx i hiF]
      exact hi
    · rw [hunion]
      ext p
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨σ j, by rw [hZnσ]; exact hj⟩
      · rintro ⟨i, hi⟩
        have hiF := hZnF i p hi
        exact ⟨F.equivFin ⟨i, hiF⟩, by rw [← hZnidx i hiF]; exact hi⟩
    · intro i j hij
      obtain ⟨p, hp1, hp2⟩ := hij
      have hiF := hZnF i p hp1
      obtain ⟨k, rfl⟩ : ∃ k, σ k = i := ⟨_, hσidx i hiF⟩
      rw [hZnσ] at hp1 ⊢
      exact hcross k j ⟨p, hp1, hp2⟩

end WangZahlLot.Obl.wz_coarse_tube_grains
