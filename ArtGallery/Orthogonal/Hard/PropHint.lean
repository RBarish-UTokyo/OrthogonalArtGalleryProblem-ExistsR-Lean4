module

public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Propagation checks with hints, on integer-coded certificates

`LCert.okPropR` decides, for every local rectangle `q` with cones, every other local rectangle `q'`
and every cone `K` of `q`, that a half-plane of `K` is negative on `q ∩ q'` or that a cone of `q'`
consists of half-planes of `K` and half-planes nonnegative on `q ∩ q'`.  For a certificate coded
by integers (`TCertI`), the kernel would decode every half-plane it compares; and searching for the
half-plane or the cone dominates the cost.  Here the check runs on the codes: cones are lists of
half-plane indices (membership is a test on natural numbers), only the half-planes that are tested
for a sign are decoded, and the search is replaced by a hint: for every pair `q, q'` whose
rectangles are not robustly apart, one code per cone `K` of `q`, `2 j` (the half-plane `j` of `K`
is negative) or `2 k + 1` (the cone `k` of `q'`).  The hints only steer the check:
`TCertI.okPropR_of_I` derives the unhinted check from any hints that pass.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

/-- A local rectangle with cones of half-plane indices. -/
abbrev LQI := LR × ℕ × List (List ℕ)

/-- Its decoding. -/
def LQI.dec (hp : ℕ → HP) (q : LQI) : LR × ℕ × List (List HP) := (q.1, q.2.1, q.2.2.map (·.map hp))

/-- The check of one cone `K` against `q'` on `X = q ∩ q'` by its code. -/
def codeI (A : LR) (hp : ℕ → HP) (K : List ℕ) (q' : LQI) (X : LR) (c : ℕ) : Bool :=
  if c % 2 = 0 then decide (c / 2 < K.length) && hpNegr A (hp (K.getD (c / 2) 0)) X
  else decide (c / 2 < q'.2.2.length) &&
    (q'.2.2.getD (c / 2) []).all fun i => decide (i ∈ K) || hpNNr A (hp i) X

/-- The check of all cones of `q` against `q'` by their codes. -/
def pairI (A : LR) (hp : ℕ → HP) (q q' : LQI) (X : LR) (hk : List ℕ) : Bool :=
  (List.range q.2.2.length).all fun i => codeI A hp (q.2.2.getD i []) q' X (hk.getD i 0)

/-- Propagation from `q` to every rectangle of a list, consuming one hint per rectangle that is
not robustly apart from `q`. -/
def propI (A : LR) (hp : ℕ → HP) (q : LQI) : List LQI → List (List ℕ) → Bool
  | [], _ => true
  | q' :: rest, hs =>
    match q.1.inter q'.1 with
    | none => false
    | some none => propI A hp q rest hs
    | some (some X) =>
      match hs with
      | [] => false
      | hk :: hs' => pairI A hp q q' X hk && propI A hp q rest hs'

/-- The default local rectangle. -/
def LQI.dflt : LQI := (⟨0, 0, (0, 0), (0, 0)⟩, 0, [])

/-- Hinted propagation from the local rectangles `a ≤ i < b`. -/
def okPropI (A : LR) (hp : ℕ → HP) (cs : List LQI) (H : List (List (List ℕ))) (a b : ℕ) : Bool :=
  (List.range' a (b - a)).all fun i =>
    (cs.getD i LQI.dflt).2.2.isEmpty || propI A hp (cs.getD i LQI.dflt) cs (H.getD i [])

theorem codeI_sound {A : LR} {hp : ℕ → HP} {K : List ℕ} {q' : LQI} {X : LR} {c : ℕ}
    (h : codeI A hp K q' X c = true) :
    (((K.map hp).any fun h => hpNegr A h X) ||
      ((LQI.dec hp q').2.2.any fun K' => K'.all fun h => decide (h ∈ K.map hp) || hpNNr A h X))
      = true := by
  unfold codeI at h
  rw [Bool.or_eq_true]
  split_ifs at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine Or.inl (List.any_eq_true.2 ⟨hp (K.getD (c / 2) 0), ?_, h.2⟩)
    rw [List.getD_eq_getElem _ _ h.1]; exact List.mem_map_of_mem (List.getElem_mem h.1)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine Or.inr (List.any_eq_true.2 ⟨(q'.2.2.getD (c / 2) []).map hp, ?_,
      List.all_eq_true.2 fun x hx => ?_⟩)
    · rw [List.getD_eq_getElem _ _ h1]
      exact List.mem_map_of_mem (f := (·.map hp)) (List.getElem_mem h1)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      have := List.all_eq_true.1 h2 i hi
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this ⊢
      rcases this with h | h
      · exact Or.inl (List.mem_map_of_mem h)
      · exact Or.inr h

theorem pairI_sound {A : LR} {hp : ℕ → HP} {q q' : LQI} {X : LR} {hk : List ℕ}
    (h : pairI A hp q q' X hk = true) :
    ((LQI.dec hp q).2.2.all fun K => (K.any fun h => hpNegr A h X) ||
      (LQI.dec hp q').2.2.any fun K' => K'.all fun h => decide (h ∈ K) || hpNNr A h X) = true := by
  rw [List.all_eq_true]
  intro K hK
  obtain ⟨K0, hK0, rfl⟩ := List.mem_map.1 hK
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hK0
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [List.getD_eq_getElem _ _ hi] at this
  exact codeI_sound this

theorem propI_sound {A : LR} {hp : ℕ → HP} {q : LQI} :
    ∀ (l : List LQI) (hs : List (List ℕ)), propI A hp q l hs = true →
      ∀ q' ∈ l, propB A (LQI.dec hp q) (LQI.dec hp q') = true
  | [], _, _, q', hq' => by simp at hq'
  | q' :: rest, hs, h, q'', hq'' => by
    unfold propI at h
    rcases List.mem_cons.1 hq'' with rfl | hq''
    · unfold propB
      split at h
      · cases h
      · rename_i hi; simp only [LQI.dec]; rw [hi]; simp
      · rename_i X hi
        simp only [LQI.dec] at h ⊢
        rw [hi]
        split at h
        · cases h
        · simp only [Bool.and_eq_true] at h
          simp only [Bool.or_eq_true]
          exact Or.inr (pairI_sound h.1)
    · split at h
      · cases h
      · exact propI_sound rest hs h q'' hq''
      · split at h
        · cases h
        · simp only [Bool.and_eq_true] at h
          exact propI_sound rest _ h.2 q'' hq''

theorem allR_of_idx {α : Type*} {P : α → Bool} {l : List α} {a b : ℕ}
    (h : ∀ i (hi : i < l.length), a ≤ i → i < b → P l[i] = true) : allR P l a b = true := by
  unfold allR
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  rw [List.getElem_take, List.getElem_drop]
  have hk' := hk
  rw [List.length_take, List.length_drop] at hk'
  exact h _ (by omega) (by omega) (by omega)

theorem idx_of_allR {α : Type*} {P : α → Bool} {l : List α} {a b : ℕ} (h : allR P l a b = true)
    {i : ℕ} (hi : i < l.length) (hai : a ≤ i) (hib : i < b) : P l[i] = true := by
  unfold allR at h
  have hk : i - a < ((l.drop a).take (b - a)).length := by
    rw [List.length_take, List.length_drop]; omega
  have := List.all_eq_true.1 h _ (List.getElem_mem hk)
  rw [List.getElem_take, List.getElem_drop] at this
  have e : l[a + (i - a)] = l[i] := by congr 1; omega
  rwa [e] at this

/-- **The hinted check implies the propagation check** of a certificate whose local rectangles
are the decodings of `cs`. -/
theorem LCert.okPropR_of_I {c : LCert} {hp : ℕ → HP} {cs : List LQI}
    (hcs : c.cs = cs.map (LQI.dec hp)) (H : List (List (List ℕ))) {a b : ℕ}
    (h : okPropI c.A hp cs H a b = true) : c.okPropR a b = true := by
  unfold LCert.okPropR
  refine allR_of_idx fun i hi hai hib => ?_
  have hi' : i < cs.length := by rw [hcs, List.length_map] at hi; exact hi
  have := List.all_eq_true.1 h i (List.mem_range'_1.2 ⟨hai, by omega⟩)
  rw [List.getD_eq_getElem _ _ hi'] at this
  have e : c.cs[i] = LQI.dec hp cs[i] := by simp only [hcs, List.getElem_map]
  unfold LCert.propQ
  rw [e]
  simp only [Bool.or_eq_true] at this ⊢
  rcases this with h1 | h1
  · exact Or.inl (by simpa [LQI.dec] using h1)
  · refine Or.inr (List.all_eq_true.2 fun q' hq' => ?_)
    rw [hcs] at hq'
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 hq'
    exact propI_sound _ _ h1 q0 hq0

/-! ### Integer keys of rectangles

The test that two rectangles are robustly apart, done in rationals by `LR.inter`, dominates the
propagation loop.  A *key* of a rectangle is a tuple of natural numbers `(X₀, X₁, B₀, V₀, B₁, V₁)`
with `X = x L + O_X`, `B = b L + O_B` and `V = (a + 1000 b) L + O_V` for its abscissae `x` and
ordinates `(a, b)` (standing for `a + b H`), with a scale `L > 0` and offsets; apartness of keys
(`apartK`) is decided by comparisons of natural numbers and implies `LR.inter = some none`.  The
keys of the rectangles of a group are checked once (`keysOK`). -/

/-- The key of a rectangle. -/
abbrev Key := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- The scale and the offsets of keys. -/
structure KeyP where
  L : ℕ
  OX : ℕ
  OB : ℕ
  OV : ℕ

/-- `k` is the key of `r`. -/
def keyEqB (P : KeyP) (r : LR) (k : Key) : Bool :=
  decide ((k.1 : ℚ) = r.x0 * P.L + P.OX) && decide ((k.2.1 : ℚ) = r.x1 * P.L + P.OX) &&
  decide ((k.2.2.1 : ℚ) = r.y0.2 * P.L + P.OB) &&
  decide ((k.2.2.2.1 : ℚ) = (r.y0.1 + r.y0.2 * 1000) * P.L + P.OV) &&
  decide ((k.2.2.2.2.1 : ℚ) = r.y1.2 * P.L + P.OB) &&
  decide ((k.2.2.2.2.2 : ℚ) = (r.y1.1 + r.y1.2 * 1000) * P.L + P.OV)

/-- The keys of a list of rectangles. -/
def keysOK (P : KeyP) (rs : List (LR × ℕ)) (ks : List Key) : Bool :=
  decide (0 < P.L) && decide (ks.length = rs.length) && (rs.zip ks).all fun p => keyEqB P p.1.1 p.2

/-- Robust apartness of two rectangles by their keys. -/
def apartK (k k' : Key) : Bool :=
  Nat.blt k.2.1 k'.1 || Nat.blt k'.2.1 k.1 ||
    (Nat.ble k.2.2.2.2.1 k'.2.2.1 && Nat.blt k.2.2.2.2.2 k'.2.2.2.1) ||
    (Nat.ble k'.2.2.2.2.1 k.2.2.1 && Nat.blt k'.2.2.2.2.2 k.2.2.2.1)

theorem apartK_inter {P : KeyP} (hL : 0 < P.L) {r r' : LR} {k k' : Key}
    (hk : keyEqB P r k = true) (hk' : keyEqB P r' k' = true) (h : apartK k k' = true) :
    r.inter r' = some none := by
  simp only [keyEqB, Bool.and_eq_true, decide_eq_true_eq] at hk hk'
  obtain ⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩ := hk
  obtain ⟨⟨⟨⟨⟨b0, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩ := hk'
  have hL' : (0 : ℚ) < P.L := by exact_mod_cast hL
  have hc : (r.x1 < r'.x0 || r'.x1 < r.x0 || AH.lt r.y1 r'.y0 || AH.lt r'.y1 r.y0) = true := by
    simp only [apartK, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    simp only [AH.lt, AH.pos, Bool.or_eq_true, decide_eq_true_eq]
    rcases h with ((h | h) | ⟨h1, h2⟩) | ⟨h1, h2⟩
    · have : (k.2.1 : ℚ) < k'.1 := by exact_mod_cast h
      left; left; left
      by_contra hc
      have : r'.x0 * P.L ≤ r.x1 * P.L := mul_le_mul_of_nonneg_right (not_lt.1 hc) hL'.le
      linarith
    · have : (k'.2.1 : ℚ) < k.1 := by exact_mod_cast h
      left; left; right
      by_contra hc
      have : r.x0 * P.L ≤ r'.x1 * P.L := mul_le_mul_of_nonneg_right (not_lt.1 hc) hL'.le
      linarith
    · have e1 : (k.2.2.2.2.1 : ℚ) ≤ k'.2.2.1 := by exact_mod_cast h1
      have e2 : (k.2.2.2.2.2 : ℚ) < k'.2.2.2.1 := by exact_mod_cast h2
      left; right
      constructor
      · by_contra hc
        have : r'.y0.2 * P.L < r.y1.2 * P.L := mul_lt_mul_of_pos_right (by linarith [not_le.1 hc]) hL'
        linarith
      · by_contra hc
        have : (r'.y0.1 + r'.y0.2 * 1000) * P.L ≤ (r.y1.1 + r.y1.2 * 1000) * P.L :=
          mul_le_mul_of_nonneg_right (by linarith [not_lt.1 hc]) hL'.le
        linarith
    · have e1 : (k'.2.2.2.2.1 : ℚ) ≤ k.2.2.1 := by exact_mod_cast h1
      have e2 : (k'.2.2.2.2.2 : ℚ) < k.2.2.2.1 := by exact_mod_cast h2
      right
      constructor
      · by_contra hc
        have : r.y0.2 * P.L < r'.y1.2 * P.L := mul_lt_mul_of_pos_right (by linarith [not_le.1 hc]) hL'
        linarith
      · by_contra hc
        have : (r.y0.1 + r.y0.2 * 1000) * P.L ≤ (r'.y1.1 + r'.y1.2 * 1000) * P.L :=
          mul_le_mul_of_nonneg_right (by linarith [not_lt.1 hc]) hL'.le
        linarith
  unfold LR.inter
  rw [if_pos hc]

/-- Propagation from `q` (key `kq`) to every rectangle of a list with keys: rectangles apart by
their keys are skipped, the others consume one hint. -/
def propK (A : LR) (hp : ℕ → HP) (q : LQI) (kq : Key) : List (LQI × Key) → List (List ℕ) → Bool
  | [], _ => true
  | (q', k') :: rest, hs =>
    if apartK kq k' then propK A hp q kq rest hs else
    match q.1.inter q'.1 with
    | none => false
    | some none => propK A hp q kq rest hs
    | some (some X) =>
      match hs with
      | [] => false
      | hk :: hs' => pairI A hp q q' X hk && propK A hp q kq rest hs'

/-- The default key. -/
def Key.dflt : Key := (0, 0, 0, 0, 0, 0)

/-- Hinted propagation with keys from the local rectangles `a ≤ i < b` (the local rectangles, their
keys and their hints are traversed together). -/
def okPropK (A : LR) (hp : ℕ → HP) (cs : List LQI) (ks : List Key) (H : List (List (List ℕ)))
    (a b : ℕ) : Bool :=
  decide (cs.length ≤ H.length) &&
    allR (fun t => t.1.1.2.2.isEmpty || propK A hp t.1.1 t.1.2 (cs.zip ks) t.2) ((cs.zip ks).zip H) a b

theorem propK_sound {A : LR} {hp : ℕ → HP} {q : LQI} {kq : Key} {P : KeyP} (hL : 0 < P.L)
    (hkq : keyEqB P q.1 kq = true) :
    ∀ (l : List (LQI × Key)) (hs : List (List ℕ)), (∀ p ∈ l, keyEqB P p.1.1 p.2 = true) →
      propK A hp q kq l hs = true → ∀ p ∈ l, propB A (LQI.dec hp q) (LQI.dec hp p.1) = true
  | [], _, _, _, p, hp' => by simp at hp'
  | (q', k') :: rest, hs, hks, h, p, hpm => by
    have hrest : ∀ p ∈ rest, keyEqB P p.1.1 p.2 = true := fun p hp => hks p (List.mem_cons_of_mem _ hp)
    unfold propK at h
    rcases List.mem_cons.1 hpm with rfl | hpm
    · by_cases ha : apartK kq k' = true
      · have hi := apartK_inter hL hkq (hks _ List.mem_cons_self) ha
        unfold propB
        simp only [LQI.dec]; rw [hi]; simp
      · rw [if_neg ha] at h
        unfold propB
        split at h
        · cases h
        · rename_i hi; simp only [LQI.dec]; rw [hi]; simp
        · rename_i X hi
          simp only [LQI.dec] at h ⊢
          rw [hi]
          split at h
          · cases h
          · simp only [Bool.and_eq_true] at h
            simp only [Bool.or_eq_true]
            exact Or.inr (pairI_sound h.1)
    · split_ifs at h
      · exact propK_sound hL hkq rest hs hrest h p hpm
      · split at h
        · cases h
        · exact propK_sound hL hkq rest hs hrest h p hpm
        · split at h
          · cases h
          · simp only [Bool.and_eq_true] at h
            exact propK_sound hL hkq rest _ hrest h.2 p hpm

theorem keysOK_get {P : KeyP} {rs : List (LR × ℕ)} {ks : List Key} (h : keysOK P rs ks = true)
    {i : ℕ} (hi : i < rs.length) : keyEqB P (rs.getD i (LR.dflt, 0)).1 (ks.getD i Key.dflt) = true := by
  simp only [keysOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨_, hl⟩, h⟩ := h
  have hi' : i < (rs.zip ks).length := by simp [hl, hi]
  have := List.all_eq_true.1 h _ (List.getElem_mem hi')
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)]
  simpa [List.getElem_zip] using this

/-- The local rectangles of an integer-coded target over the rectangles of a group. -/
def TCertI.csI (gs : List GZ) (c : TCertI) : List LQI :=
  (groupLR gs).zipWith (fun rk Ks => (rk.1, rk.2, Ks)) c.cones

theorem TCertI.cert_cs (gs : List GZ) (c : TCertI) :
    (c.toT.cert gs).cs = (c.csI gs).map (LQI.dec c.hp) := by
  simp only [TCert.cert, TCertI.toT, TCertI.csI]
  generalize groupLR gs = l
  generalize c.cones = cs
  induction l generalizing cs with
  | nil => simp
  | cons r l ih => cases cs with
    | nil => simp
    | cons K cs => simp [List.zipWith_cons_cons, ih, LQI.dec]

/-- **Hinted propagation of an integer-coded target certificate, with keys.** -/
theorem TCertI.okPropR_of_K {T : TCert} (c : TCertI) (hT : T = c.toT) (gs : List GZ)
    {P : KeyP} {ks : List Key} (hks : keysOK P (groupLR gs) ks = true)
    (H : List (List (List ℕ))) {a b : ℕ}
    (h : okPropK c.toT.A c.hp (c.csI gs) ks H a b = true) : (T.cert gs).okPropR a b = true := by
  subst hT
  have hL : 0 < P.L := by
    simp only [keysOK, Bool.and_eq_true, decide_eq_true_eq] at hks; exact hks.1.1
  have hlen : (c.csI gs).length ≤ (groupLR gs).length := by
    simp [TCertI.csI, List.length_zipWith]
  have hksl : (groupLR gs).length ≤ ks.length := by
    simp only [keysOK, Bool.and_eq_true, decide_eq_true_eq] at hks; omega
  -- the key of the local rectangle `i`
  have hkey : ∀ i (hi : i < (c.csI gs).length),
      keyEqB P ((c.csI gs)[i]).1 (ks.getD i Key.dflt) = true := by
    intro i hi
    have := keysOK_get hks (show i < (groupLR gs).length by omega)
    have e : ((c.csI gs)[i]).1 = ((groupLR gs).getD i (LR.dflt, 0)).1 := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp [TCertI.csI, List.getElem_zipWith]
    rw [e]; exact this
  simp only [okPropK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hHl, h⟩ := h
  unfold LCert.okPropR
  refine allR_of_idx fun i hi hai hib => ?_
  have hcs := TCertI.cert_cs gs c
  have hi' : i < (c.csI gs).length := by rw [hcs, List.length_map] at hi; exact hi
  have hiz : i < ((c.csI gs).zip ks |>.zip H).length := by simp; omega
  have := idx_of_allR h hiz hai hib
  simp only [List.getElem_zip] at this
  have e : (c.toT.cert gs).cs[i] = LQI.dec c.hp (c.csI gs)[i] := by simp only [hcs, List.getElem_map]
  unfold LCert.propQ
  rw [e]
  simp only [Bool.or_eq_true] at this ⊢
  rcases this with h1 | h1
  · exact Or.inl (by simpa [LQI.dec] using h1)
  · refine Or.inr (List.all_eq_true.2 fun q' hq' => ?_)
    rw [hcs] at hq'
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 hq'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq0
    have hzip : ((c.csI gs)[j], ks.getD j Key.dflt) ∈ (c.csI gs).zip ks := by
      have hj' : j < ((c.csI gs).zip ks).length := by simp; omega
      have := List.getElem_mem hj'
      rw [List.getElem_zip] at this
      rwa [List.getD_eq_getElem _ _ (by omega)]
    have hall : ∀ p ∈ (c.csI gs).zip ks, keyEqB P p.1.1 p.2 = true := by
      intro p hp
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hp
      rw [List.getElem_zip]
      have hm1 : m < (c.csI gs).length := by simp at hm; omega
      have := hkey m hm1
      rwa [List.getD_eq_getElem _ _ (by simp at hm; omega)] at this
    have hki := hkey i hi'
    rw [List.getD_eq_getElem _ _ (by omega)] at hki
    have key := propK_sound (A := c.toT.A) (hp := c.hp) hL hki ((c.csI gs).zip ks) _ hall
      h1 _ hzip
    exact key

/-- **Hinted propagation of an integer-coded target certificate.** -/
theorem TCertI.okPropR_of_I {T : TCert} (c : TCertI) (hT : T = c.toT) (gs : List GZ)
    (H : List (List (List ℕ))) {a b : ℕ}
    (h : okPropI c.toT.A c.hp (c.csI gs) H a b = true) : (T.cert gs).okPropR a b = true := by
  subst hT
  exact LCert.okPropR_of_I (TCertI.cert_cs gs c) H h

end

end ArtGallery.Orthogonal.Hard
