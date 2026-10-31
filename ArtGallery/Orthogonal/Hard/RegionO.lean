module

public import ArtGallery.Orthogonal.Hard.ZonesO

/-!
# The region of the orthogonal polygon

**`filledO`**: the region of the orthogonal polygon `polyO n Φ` is the union of the rectangles
`regionRectsO n Φ`: the hall `[x_L, x_R] × [−1/4, 2H − 1/4]`, the floor half comb (the zones of
the floor features `zfO` and the gap rectangles of the floor strip `[−1, −1/4]`) and the ceiling
half comb (the zones `zcO` of the ceiling features and the gap rectangles, mirrored through the
origin, of the ceiling strip `[2H − 1/4, 2H]`).  It is `filled_combs` for the zones of
`ArtGallery/Orthogonal/Hard/ZonesO.lean`, ordered from left to right (floor) and from right to
left (ceiling) with gaps between their boxes.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational Set

/-! ### Separation of the templates of a group by more than `1/4` -/

theorem varFloor_sep4 : pairwiseB (fun f g => decide (f.xmax + 1 / 4 < g.xmin)) oVarFloor = true := by
  decide +kernel

theorem slotFloor_sep4 :
    allKinds.all (fun k => pairwiseB (fun f g => decide (f.xmax + 1 / 4 < g.xmin)) (oSlotFloor k)) =
      true := by decide +kernel

theorem varCeil_sep4 : pairwiseB (fun f g => decide (g.xmax + 1 / 4 < f.xmin)) oVarCeil = true := by
  decide +kernel

theorem inputCeil_sep4 (pos : Bool) :
    pairwiseB (fun f g => decide (g.xmax + 1 / 4 < f.xmin)) (oInputCeil pos) = true := by
  cases pos <;> decide +kernel

theorem oBasin_mem : oBasin ∈ allFloorTmpls := List.mem_cons_self

/-! ### Ordered zones -/

theorem zord_of {s e : ℝ} : ∀ {zs : List FZone}, s < e → (∀ Z ∈ zs, s < Z.L ∧ Z.R < e) →
    zs.Pairwise (fun Z Z' => Z.R < Z'.L) → ZOrd s zs e
  | [], h, _, _ => h
  | Z :: zs, h, hb, hp => by
    have hp' := List.pairwise_cons.1 hp
    exact ⟨(hb Z (by simp)).1, zord_of (hb Z (by simp)).2
      (fun Z' hZ' => ⟨hp'.1 Z' hZ', (hb Z' (by simp [hZ'])).2⟩) hp'.2⟩

theorem flatMap_congr' {α β : Type*} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem fzone_lt {t t' : ITmpl} (ht : t ∈ allFloorTmpls) (ht' : t' ∈ allFloorTmpls) {H ox ox' : ℚ}
    (h : ox + t.xmax + 1 / 4 < ox' + t'.xmin) : (fzone t H ox).R < (fzone t' H ox').L := by
  rw [fzone_R ht, fzone_L ht']
  exact_mod_cast (show ox + t.xmax + 1 / 8 < ox' + t'.xmin - 1 / 8 by linarith)

theorem czone_lt {t t' : ITmpl} (ht : t ∈ allCeilTmpls) (ht' : t' ∈ allCeilTmpls) {H b b' : ℚ}
    (h : b' + t'.xmax + 1 / 4 < b + t.xmin) : (czone t H b).R < (czone t' H b').L := by
  rw [czone_R ht, czone_L ht']
  exact neg_lt_neg (by exact_mod_cast (show b' + t'.xmax + 1 / 8 < b + t.xmin - 1 / 8 by linarith))

variable (n : ℕ) (Φ : List Constraint)

/-! ### The zones -/

/-- The zones of the floor features, from left to right. -/
noncomputable def zfO : List FZone :=
  [fzone oBasin (paramH n Φ : ℚ) (xL n Φ)] ++
    (List.range n).flatMap (fun k => oVarFloor.map (fun t => fzone t (paramH n Φ : ℚ) (varA Φ k))) ++
    (List.range (paramC Φ)).flatMap (fun c =>
      (oSlotFloor (cKind (gadAt Φ c))).map (fun t => fzone t (paramH n Φ : ℚ) (slotG n Φ c)))

/-- The zones of the ceiling features (mirrored through the origin), from right to left. -/
noncomputable def zcO : List FZone :=
  (inputsO n Φ).reverse.flatMap (fun i => (oInputCeil i.pos).map (fun t =>
    czone t (paramH n Φ : ℚ) i.b)) ++
    (List.range n).reverse.flatMap (fun k => oVarCeil.map (fun t =>
      czone t (paramH n Φ : ℚ) (varA Φ k))) ++
    (List.range n).reverse.flatMap (fun k => ((inputsO n Φ).filter (fun i => i.var == k)).map
      (fun i => nzone (varA Φ k) i.b i.ge (paramH n Φ : ℚ)))

/-- The rectangles of the region of the orthogonal polygon. -/
noncomputable def regionRectsO : List Rect :=
  combRects (xL n Φ : ℝ) (xR n Φ : ℝ) (-1) (2 * ((paramH n Φ : ℚ) : ℝ)) (-1 / 4)
    (2 * ((paramH n Φ : ℚ) : ℝ) - 1 / 4) (zfO n Φ) (zcO n Φ)

variable {n Φ}

/-! ### Floor -/

theorem zfO_f : (zfO n Φ).map FZone.f = (floorFeatsO n Φ).map (List.map ratPoint) := by
  simp only [zfO, floorFeatsO, List.map_append, List.map_cons, List.map_nil, List.map_flatMap,
    List.map_map]
  congr 1
  · congr 1
    · simp only [Function.comp_apply, fzone_f oBasin_mem]
    · refine flatMap_congr' (fun k _ => List.map_congr_left (fun t ht => ?_))
      simp only [Function.comp]
      rw [fzone_f (mem_allFloorTmpls_var ht)]
  · refine flatMap_congr' (fun c _ => List.map_congr_left (fun t ht => ?_))
    simp only [Function.comp]
    rw [fzone_f (mem_allFloorTmpls_slot ht)]

theorem zfO_good : ∀ Z ∈ zfO n Φ, Z.Good (-1) (-1 / 4) := by
  have hH := paramH_ge_q n Φ
  intro Z hZ
  simp only [zfO, List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_range,
    List.mem_map] at hZ
  rcases hZ with (rfl | ⟨k, -, t, ht, rfl⟩) | ⟨c, -, t, ht, rfl⟩
  · exact fzone_good oBasin_mem hH _
  · exact fzone_good (mem_allFloorTmpls_var ht) hH _
  · exact fzone_good (mem_allFloorTmpls_slot ht) hH _

theorem zfO_bounds : ∀ Z ∈ zfO n Φ, (xL n Φ : ℝ) < Z.L ∧ Z.R < (xR n Φ : ℝ) := by
  have hxL := xL_neg n Φ
  have hxR := xR_pos n Φ
  intro Z hZ
  simp only [zfO, List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_range,
    List.mem_map] at hZ
  rcases hZ with (rfl | ⟨k, hk, t, ht, rfl⟩) | ⟨c, hc, t, ht, rfl⟩
  · have b := basin_range
    rw [fzone_L oBasin_mem, fzone_R oBasin_mem]
    exact ⟨by exact_mod_cast (show xL n Φ < xL n Φ + oBasin.xmin - 1 / 8 by linarith),
      by exact_mod_cast (show xL n Φ + oBasin.xmax + 1 / 8 < xR n Φ by linarith)⟩
  · have b := varFloor_x ht
    have h1 := var_lt_xR (Φ := Φ) hk
    have h2 := varA_nonneg Φ k
    have hH := paramH_ge_q n Φ
    rw [fzone_L (mem_allFloorTmpls_var ht), fzone_R (mem_allFloorTmpls_var ht)]
    exact ⟨by exact_mod_cast (show xL n Φ < (varA Φ k : ℚ) + t.xmin - 1 / 8 by linarith),
      by exact_mod_cast (show (varA Φ k : ℚ) + t.xmax + 1 / 8 < xR n Φ by linarith)⟩
  · have b := slotFloor_x ht
    have h1 := slot_lt_xR (n := n) hc
    have h2 := slotG_nonneg n Φ c
    rw [fzone_L (mem_allFloorTmpls_slot ht), fzone_R (mem_allFloorTmpls_slot ht)]
    exact ⟨by exact_mod_cast (show xL n Φ < (slotG n Φ c : ℚ) + t.xmin - 1 / 8 by linarith),
      by exact_mod_cast (show (slotG n Φ c : ℚ) + t.xmax + 1 / 8 < xR n Φ by linarith)⟩

theorem zfO_pw : (zfO n Φ).Pairwise (fun Z Z' => Z.R < Z'.L) := by
  have hC : (0 : ℚ) ≤ paramC Φ := by positivity
  unfold zfO
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨List.pairwise_singleton _ _, ?_, ?_⟩, ?_, ?_⟩
  · -- variables
    rw [List.pairwise_flatMap]
    refine ⟨fun k _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      refine (pairwiseB_sound varFloor_sep4).imp_of_mem (fun {f g} hf hg hfg => ?_)
      have := of_decide_eq_true hfg
      exact fzone_lt (mem_allFloorTmpls_var hf) (mem_allFloorTmpls_var hg) (by linarith)
    · refine List.pairwise_lt_range.imp (fun {k k'} hkk => ?_)
      intro Z hZ Z' hZ'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hZ
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hZ'
      have h := s2_var (Φ := Φ) hkk
      have b1 := varFloor_x ht
      have b2 := varFloor_x ht'
      exact fzone_lt (mem_allFloorTmpls_var ht) (mem_allFloorTmpls_var ht')
        (by linarith [b1.2, b2.1])
  · -- basin vs variables
    intro Z hZ Z' hZ'
    rw [List.mem_singleton] at hZ
    subst hZ
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hZ'
    obtain ⟨k, hk, t, ht, rfl⟩ := hZ'
    have b1 := basin_range
    have b2 := varFloor_x ht
    have h2 := varA_nonneg Φ k
    have hxL := xL_neg n Φ
    exact fzone_lt oBasin_mem (mem_allFloorTmpls_var ht) (by linarith [b1.2, b2.1])
  · -- slots
    rw [List.pairwise_flatMap]
    refine ⟨fun c _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      have hs := slotFloor_sep4
      simp only [List.all_eq_true] at hs
      refine (pairwiseB_sound (hs _ (mem_allKinds _))).imp_of_mem
        (fun {f g} hf hg hfg => ?_)
      have := of_decide_eq_true hfg
      exact fzone_lt (mem_allFloorTmpls_slot hf) (mem_allFloorTmpls_slot hg) (by linarith)
    · refine List.pairwise_lt_range.imp (fun {c c'} hcc => ?_)
      intro Z hZ Z' hZ'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hZ
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hZ'
      have := s2_slot (n := n) (Φ := Φ) hcc
      have b1 := slotFloor_x ht
      have b2 := slotFloor_x ht'
      exact fzone_lt (mem_allFloorTmpls_slot ht) (mem_allFloorTmpls_slot ht')
        (by linarith [b1.2, b2.1])
  · -- basin and variables vs slots
    intro Z hZ Z' hZ'
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hZ'
    obtain ⟨c, hc, t', ht', rfl⟩ := hZ'
    have b2 := slotFloor_x ht'
    rcases List.mem_append.1 hZ with hZ | hZ
    · rw [List.mem_singleton] at hZ
      subst hZ
      have b1 := basin_range
      have hxL := xL_neg n Φ
      have h0 := slotG_nonneg n Φ c
      exact fzone_lt oBasin_mem (mem_allFloorTmpls_slot ht') (by linarith [b1.2, b2.1])
    · simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hZ
      obtain ⟨k, hk, t, ht, rfl⟩ := hZ
      have b1 := varFloor_x ht
      have := s2_var_slot (Φ := Φ) (c := c) hk
      have hH := paramH_ge_q n Φ
      exact fzone_lt (mem_allFloorTmpls_var ht) (mem_allFloorTmpls_slot ht')
        (by linarith [b1.2, b2.1])

/-! ### Ceiling -/

theorem zcO_f : (zcO n Φ).map FZone.f =
    ((ceilFeatsO n Φ).map (List.map ratPoint)).map (List.map (fun q => -q)) := by
  simp only [zcO, ceilFeatsO, List.map_append, List.map_flatMap, List.map_map]
  congr 1
  · congr 1
    · refine flatMap_congr' (fun i _ => List.map_congr_left (fun t ht => ?_))
      simp only [Function.comp]
      rw [czone_f (mem_allCeilTmpls_input ht)]
    · refine flatMap_congr' (fun k _ => List.map_congr_left (fun t ht => ?_))
      simp only [Function.comp]
      rw [czone_f (mem_allCeilTmpls_var ht)]
  · refine flatMap_congr' (fun k _ => List.map_congr_left (fun i _ => ?_))
    simp only [Function.comp]
    rw [nzone_f]

theorem zcO_good : ∀ Z ∈ zcO n Φ,
    Z.Good (-(2 * ((paramH n Φ : ℚ) : ℝ))) (-(2 * ((paramH n Φ : ℚ) : ℝ) - 1 / 4)) := by
  have hH := paramH_ge_q n Φ
  intro Z hZ
  simp only [zcO, List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range,
    List.mem_map, List.mem_filter, beq_iff_eq] at hZ
  rcases hZ with (⟨i, -, t, ht, rfl⟩ | ⟨k, -, t, ht, rfl⟩) | ⟨k, hk, i, ⟨hi, -⟩, rfl⟩
  · exact czone_good (mem_allCeilTmpls_input ht) hH _
  · exact czone_good (mem_allCeilTmpls_var ht) hH _
  · obtain ⟨d1, d2⟩ := inputO_delta hi hk
    exact nzone_good hH d1 d2 i.ge

theorem zcO_bounds : ∀ Z ∈ zcO n Φ, -(xR n Φ : ℝ) < Z.L ∧ Z.R < -(xL n Φ : ℝ) := by
  have hH := paramH_ge_q n Φ
  have hxL := xL_neg n Φ
  have hxR := xR_pos n Φ
  intro Z hZ
  simp only [zcO, List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range,
    List.mem_map, List.mem_filter, beq_iff_eq] at hZ
  rcases hZ with (⟨i, hi, t, ht, rfl⟩ | ⟨k, hk, t, ht, rfl⟩) | ⟨k, hk, i, ⟨hi, -⟩, rfl⟩
  · have hb := inputO_b_bounds hi
    have h0 : (0 : ℚ) ≤ paramX0 n Φ := by positivity
    have hx := inputCeil_x ht
    rw [czone_L (mem_allCeilTmpls_input ht), czone_R (mem_allCeilTmpls_input ht)]
    exact ⟨neg_lt_neg (by exact_mod_cast (show i.b + t.xmax + 1 / 8 < xR n Φ by linarith)),
      neg_lt_neg (by exact_mod_cast (show xL n Φ < i.b + t.xmin - 1 / 8 by linarith))⟩
  · have h1 := var_lt_xR (Φ := Φ) hk
    have h2 := varA_nonneg Φ k
    have hx := varCeil_x ht
    rw [czone_L (mem_allCeilTmpls_var ht), czone_R (mem_allCeilTmpls_var ht)]
    exact ⟨neg_lt_neg (by exact_mod_cast (show (varA Φ k : ℚ) + t.xmax + 1 / 8 < xR n Φ by
        linarith)),
      neg_lt_neg (by exact_mod_cast (show xL n Φ < (varA Φ k : ℚ) + t.xmin - 1 / 8 by linarith))⟩
  · obtain ⟨d1, d2⟩ := inputO_delta hi hk
    obtain ⟨h3, h4⟩ := inputO_nookX hi hk
    have h5 := s4_xL n Φ
    have h6 : (0 : ℚ) ≤ paramC Φ := by positivity
    have e1 := nzone_L hH d1 d2 i.ge
    have e2 := nzone_R hH d1 d2 i.ge
    refine ⟨lt_of_lt_of_le ?_ e1, lt_of_le_of_lt e2 ?_⟩
    · exact neg_lt_neg (by exact_mod_cast (show nookX (varA Φ k) i.b i.ge + 7 < xR n Φ by
        linarith))
    · exact neg_lt_neg (by exact_mod_cast (show xL n Φ < nookX (varA Φ k) i.b i.ge - 3 by
        linarith))

theorem zcO_pw : (zcO n Φ).Pairwise (fun Z Z' => Z.R < Z'.L) := by
  have hH := paramH_ge_q n Φ
  have hC : (0 : ℚ) ≤ paramC Φ := by positivity
  refine List.Pairwise.imp_of_mem (R := fun Z Z' => Z ∈ zcO n Φ → Z' ∈ zcO n Φ → Z.R < Z'.L)
    (fun ha hb h => h ha hb) ?_
  unfold zcO
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- inputs
    rw [List.pairwise_flatMap]
    refine ⟨fun i _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      refine (pairwiseB_sound (inputCeil_sep4 i.pos)).imp_of_mem
        (fun {f g} hf hg hfg _ _ => ?_)
      have := of_decide_eq_true hfg
      exact czone_lt (mem_allCeilTmpls_input hf) (mem_allCeilTmpls_input hg) (by linarith)
    · rw [List.pairwise_reverse]
      refine inputsO_pw.imp (fun {i j} hij => ?_)
      intro Z hZ Z' hZ' _ _
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hZ
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hZ'
      have b1 := inputCeil_x ht
      have b2 := inputCeil_x ht'
      exact czone_lt (mem_allCeilTmpls_input ht) (mem_allCeilTmpls_input ht')
        (by linarith [b1.1, b2.2])
  · -- variables
    rw [List.pairwise_flatMap]
    refine ⟨fun k _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      refine (pairwiseB_sound varCeil_sep4).imp_of_mem (fun {f g} hf hg hfg _ _ => ?_)
      have := of_decide_eq_true hfg
      exact czone_lt (mem_allCeilTmpls_var hf) (mem_allCeilTmpls_var hg) (by linarith)
    · rw [List.pairwise_reverse]
      refine List.pairwise_lt_range.imp (fun {k k'} hkk => ?_)
      intro Z hZ Z' hZ' _ _
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hZ
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hZ'
      have := s2_var (Φ := Φ) hkk
      have b1 := varCeil_x ht
      have b2 := varCeil_x ht'
      exact czone_lt (mem_allCeilTmpls_var ht) (mem_allCeilTmpls_var ht')
        (by linarith [b1.1, b2.2])
  · -- inputs vs variables
    intro Z hZ Z' hZ' _ _
    simp only [List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map] at hZ hZ'
    obtain ⟨i, hi, t, ht, rfl⟩ := hZ
    obtain ⟨k, hk, t', ht', rfl⟩ := hZ'
    have hb := inputO_b_bounds hi
    have hv := s2_var_slot (Φ := Φ) (c := 0) hk
    have : (slotG n Φ 0 : ℚ) = paramX0 n Φ := by simp [slotG]
    have b1 := inputCeil_x ht
    have b2 := varCeil_x ht'
    exact czone_lt (mem_allCeilTmpls_input ht) (mem_allCeilTmpls_var ht')
      (by linarith [b1.1, b2.2])
  · -- copy nooks
    rw [List.pairwise_flatMap]
    refine ⟨fun k hk => ?_, ?_⟩
    · rw [List.mem_reverse, List.mem_range] at hk
      rw [List.pairwise_map]
      refine (inputsO_pw.filter _).imp_of_mem (fun {i j} hi hj hij _ _ => ?_)
      simp only [List.mem_filter, beq_iff_eq] at hi hj
      obtain ⟨d1, d2⟩ := inputO_delta hi.1 hk
      obtain ⟨d3, d4⟩ := inputO_delta hj.1 hk
      have hs := s3_same (a := (varA Φ k : ℚ)) hij (copyE_bounds i.ge) (copyE_bounds j.ge)
      refine lt_of_le_of_lt (nzone_R hH d1 d2 i.ge) (lt_of_lt_of_le ?_ (nzone_L hH d3 d4 j.ge))
      exact neg_lt_neg (by exact_mod_cast (show nookX (varA Φ k) j.b j.ge + 7 <
        nookX (varA Φ k) i.b i.ge - 3 by unfold nookX; linarith))
    · rw [List.pairwise_reverse]
      refine List.pairwise_lt_range.imp_of_mem (fun {k k'} _ hk' hkk => ?_)
      rw [List.mem_range] at hk'
      intro Z hZ Z' hZ' _ _
      simp only [List.mem_map, List.mem_filter, beq_iff_eq] at hZ hZ'
      obtain ⟨j, ⟨hj, -⟩, rfl⟩ := hZ
      obtain ⟨i, ⟨hi, -⟩, rfl⟩ := hZ'
      obtain ⟨d1, d2⟩ := inputO_delta hj hk'
      obtain ⟨d3, d4⟩ := inputO_delta hi (hkk.trans hk')
      obtain ⟨c, hc, δ, hδ0, hδ1, hb⟩ := inputsO_b hi
      obtain ⟨c', hc', δ', hδ0', hδ1', hb'⟩ := inputsO_b hj
      have hs := s3_diff (n := n) (Φ := Φ) (c := c) hkk hc' hδ0 hδ1' (copyE_bounds i.ge)
        (copyE_bounds j.ge)
      refine lt_of_le_of_lt (nzone_R hH d1 d2 j.ge) (lt_of_lt_of_le ?_ (nzone_L hH d3 d4 i.ge))
      exact neg_lt_neg (by exact_mod_cast (show nookX (varA Φ k) i.b i.ge + 7 <
        nookX (varA Φ k') j.b j.ge - 3 by unfold nookX; rw [hb, hb']; linarith))
  · -- wedges vs copy nooks
    intro Z hZ Z' hZ' _ _
    simp only [List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map,
      List.mem_filter, beq_iff_eq, List.mem_append] at hZ hZ'
    obtain ⟨k, hk, i, ⟨hi, -⟩, rfl⟩ := hZ'
    obtain ⟨d1, d2⟩ := inputO_delta hi hk
    obtain ⟨h3, h4⟩ := inputO_nookX hi hk
    have hL := nzone_L hH d1 d2 i.ge
    rcases hZ with ⟨j, hj, t, ht, rfl⟩ | ⟨k', hk', t, ht, rfl⟩
    · have hb := inputO_b_bounds hj
      have h0 : (0 : ℚ) ≤ paramX0 n Φ := by positivity
      have b1 := inputCeil_x ht
      rw [czone_R (mem_allCeilTmpls_input ht)]
      refine lt_of_lt_of_le (neg_lt_neg ?_) hL
      exact_mod_cast (show nookX (varA Φ k) i.b i.ge + 7 < j.b + t.xmin - 1 / 8 by linarith)
    · have h0 := varA_nonneg Φ k'
      have b1 := varCeil_x ht
      rw [czone_R (mem_allCeilTmpls_var ht)]
      refine lt_of_lt_of_le (neg_lt_neg ?_) hL
      exact_mod_cast (show nookX (varA Φ k) i.b i.ge + 7 < (varA Φ k' : ℚ) + t.xmin - 1 / 8 by
        linarith)

/-! ### The region -/

/-- **The region of the orthogonal polygon** is the union of the rectangles `regionRectsO`. -/
theorem filledO (n : ℕ) (Φ : List Constraint) :
    (Polygon.mk ((polyO n Φ).map ratPoint)).filled = RU (regionRectsO n Φ) := by
  have hP := simpleO n Φ
  rw [polyO_map] at hP ⊢
  have hx : (xL n Φ : ℝ) < xR n Φ := by exact_mod_cast xL_lt_xR n Φ
  have hH : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := by exact_mod_cast paramH_ge_q n Φ
  refine filled_combs hx (by norm_num) (by linarith) (by linarith) _ _ (zfO n Φ) (zcO n Φ)
    zfO_f zfO_good ?_ zcO_f zcO_good ?_ hP
  · exact zord_of hx zfO_bounds zfO_pw
  · exact zord_of (by linarith) zcO_bounds zcO_pw

end

end ArtGallery.Orthogonal.Hard
