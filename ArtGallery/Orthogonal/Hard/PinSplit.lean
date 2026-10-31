module

public import ArtGallery.Orthogonal.Hard.PinGroup

/-!
# Pin checks in parts

A kernel check `pinB … = true` of a large pin target keeps every intermediate result of the
evaluation in the kernel's caches, which are per declaration.  `pinB_of_parts` assembles the check
from parts that are proved as separate declarations:

* `LCert.okBase`: the conditions of `LCert.ok` other than propagation;
* `LCert.okPropR c a b`: the propagation from the local rectangles `a ≤ i < b`;
* `pinHeadB`: the number of cones and the slab;
* `pinJR … a b`: the conditions against the witnesses `a ≤ j < b`.

Ranges are joined by `allR_join`.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational

/-- `P` holds on the entries `a ≤ i < b` of `l`. -/
def allR {α : Type*} (P : α → Bool) (l : List α) (a b : ℕ) : Bool := ((l.drop a).take (b - a)).all P

theorem allR_join {α : Type*} {P : α → Bool} {l : List α} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : allR P l a b = true) (h2 : allR P l b c = true) : allR P l a c = true := by
  unfold allR at *
  have e : (l.drop a).take (c - a) = (l.drop a).take (b - a) ++ (l.drop b).take (c - b) := by
    have hb : l.drop b = (l.drop a).drop (b - a) := by rw [List.drop_drop]; congr 1; omega
    rw [hb, show c - a = (b - a) + (c - b) by omega, List.take_add]
  rw [e, List.all_append, h1, h2]; rfl

theorem all_of_allR {α : Type*} {P : α → Bool} {l : List α} {n : ℕ} (hn : l.length ≤ n)
    (h : allR P l 0 n = true) : l.all P = true := by
  unfold allR at h
  rwa [List.drop_zero, Nat.sub_zero, List.take_of_length_le hn] at h

/-- The conditions of `LCert.ok` other than propagation. -/
def LCert.okBase (c : LCert) : Bool :=
  (c.cs.flatMap (fun q => q.2.2.flatten) ++ c.C.getD []).all (starB c.A) &&
  c.A.corners.all (c.U.getD c.Ab LBox.default).memB && decide (c.Ab < c.U.length) &&
  c.cs.all (fun q => baseB c.A q && decide (q.2.1 < c.U.length) &&
    match q.1.faces (c.U.getD q.2.1 LBox.default) with
    | none => false
    | some fs => fs.all fun e => faceB c.A c.C q.2.2 e)

/-- The propagation condition of a local rectangle. -/
def LCert.propQ (c : LCert) (q : LR × ℕ × List (List HP)) : Bool :=
  q.2.2.isEmpty || c.cs.all fun q' => propB c.A q q'

/-- Propagation from the local rectangles `a ≤ i < b`. -/
def LCert.okPropR (c : LCert) (a b : ℕ) : Bool := allR c.propQ c.cs a b

theorem LCert.ok_of_parts {c : LCert} (h0 : c.okBase = true) {n : ℕ} (hn : c.cs.length ≤ n)
    (h : c.okPropR 0 n = true) : c.ok = true := by
  have hp := all_of_allR hn h
  show (c.okBase && c.cs.all fun q => q.2.2.isEmpty || c.cs.all fun q' => propB c.A q q') = true
  rw [h0]; exact hp

/-- The number of cones and the slab of a pin target. -/
def pinHeadB (gs : List GZ) (P : PinT) : Bool :=
  decide (P.T.cones.length = (groupLR gs).length) && P.T.slabB

/-- The condition of a pin target against the witness `j`. -/
def pinJQ (gs : List GZ) (Ws : List WCert) (rks : List ℕ) (sps : List LR) (P : PinT) (j : ℕ) :
    Bool :=
  decide (j = P.owner) || decide (j ∈ P.exempt) ||
    if rks.getD j 0 < rks.getD P.owner 0 then rectUnseenB (P.T.cert gs) (sps.getD j LR.dflt)
    else disjB (P.T.cert gs) ((Ws.getD j WCert.dflt).cert gs) &&
        tescSepB (treeOfJ P.trees j) P.T (Ws.getD j WCert.dflt).toT

/-- The conditions of a pin target against the witnesses `a ≤ j < b`. -/
def pinJR (gs : List GZ) (Ws : List WCert) (rks : List ℕ) (sps : List LR) (P : PinT) (a b : ℕ) :
    Bool :=
  allR (pinJQ gs Ws rks sps P) (List.range Ws.length) a b

/-- **A pin check from its parts.** -/
theorem pinB_of_parts {gs : List GZ} {Ws : List WCert} {rks : List ℕ} {sps : List LR} {P : PinT}
    (hok : (P.T.cert gs).ok = true) (hhead : pinHeadB gs P = true) {n : ℕ} (hn : Ws.length ≤ n)
    (hj : pinJR gs Ws rks sps P 0 n = true) : pinB gs Ws rks sps P = true := by
  have hall := all_of_allR (by simpa using hn) hj
  unfold pinHeadB at hhead
  unfold pinB
  rw [hok, Bool.true_and]
  unfold pinJQ at hall
  rw [hall, Bool.and_true]; exact hhead

end

end ArtGallery.Orthogonal.Hard
