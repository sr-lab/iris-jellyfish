(* This file contains the specification of the lock module implemented as a
   simple spin lock and discussed in section 7.6 in the invariants and ghost
   state chapter of the Iris Lecture Notes.
*)

(* Contains definitions of the weakest precondition assertion, and its basic rules. *)
From iris.program_logic Require Export weakestpre.

(* Instantiation of Iris with the particular language. The notation file
   contains many shorthand notations for the programming language constructs, and
   the lang file contains the actual language syntax. *)
From iris.heap_lang Require Export notation lang.

(* Files related to the interactive proof mode. The first import includes the
   general tactics of the proof mode. The second provides some more specialized
   tactics particular to the instantiation of Iris to a particular programming
   language. *)
From iris.proofmode Require Export proofmode.
From iris.heap_lang Require Import proofmode.

(* Definition of invariants and their rules (expressed using the fancy update modality). *)
From iris.base_logic.lib Require Export invariants.

(* The exclusive resource algebra. *)
From iris.algebra Require Import excl.

(* The following line imports some Coq configuration we commonly use in Iris
   projects, mostly with the goal of catching common mistakes. *)
From iris.prelude Require Import options.

Class lockG Σ := lock_G :> inG Σ (exclR unitR).

Section lock_model.
(* In order to do the proof we need to assume certain things about the
   instantiation of Iris. The particular, even the heap is handled in an
   analogous way as other ghost state. This line states that we assume the Iris
   instantiation has sufficient structure to manipulate the heap, e.g., it
   allows us to use the points-to predicate, and that the ghost state includes
   the exclusive resource algebra over the singleton set (represented using the
   unitR type). *)

  Context `{heapGS Σ, lockG Σ}.

  (* We use a ghost name with a token to model whether the lock is locked or not.
     The the token is just exclusive ownerwhip of unit value. *)
  Definition locked γ := own γ (Excl ()).

  (* The name of a lock. *)
  Definition lockN (l : val) := nroot .@ "lock" .@ l.

  (* The lock invariant *)
  Definition is_lock γ (v : val) P :=
    (∃ (ℓ : loc), ⌜v = #ℓ⌝ ∧ inv (lockN v) (ℓ ↦ #false ∗ P ∗ locked γ ∨ ℓ ↦ #true))%I.

  (* The is_lock predicate is persistent *)
  Global Instance is_lock_persistent γ l Φ : Persistent (is_lock γ l Φ).
  Proof. apply _. Qed.

End lock_model.

Section lock_code.

  (* The standard spin lock code *)
  Definition newlock : val := λ: <>, ref #false.
  Definition acquire : val :=
    rec: "acquire" "l" :=
      if: CAS "l" #false #true then #() else "acquire" "l".
  Definition release : val := λ: "l", "l" <- #false.

End lock_code.

Section lock_spec.
  Context `{heapGS Σ, lockG Σ}.

  Lemma newlock_spec P :
    {{{ P }}} newlock #() {{{ l, RET l; ∃ γ, is_lock γ l P }}}.
  Proof.
    iIntros (φ) "Hi Hcont".
    rewrite /newlock.
    wp_lam.
    wp_alloc l as "HPt".
    iMod (own_alloc (Excl ())) as (γ) "Hld"; first done.
    iMod (inv_alloc _ _
           ((l ↦ (#false) ∗ P ∗ locked γ) ∨ l ↦ (#true))%I with "[-Hcont]")
      as "Hinv"; last eauto.
    { iNext; iLeft; iFrame. }
    iApply "Hcont".
    iExists γ. iModIntro. iExists l. iSplit; first done.
    iFrame.
  Qed.

  Lemma acquire_spec E γ l P :
    nclose (lockN l) ⊆ E →
    {{{ is_lock γ l P }}} acquire l @ E {{{ v, RET #v; P ∗ locked γ }}}.
  Proof.
    iIntros (HE φ) "#Hi Hcont"; rewrite /acquire.
    iDestruct "Hi" as (ℓ ->) "Hinv".
    iLöb as "IH".
    wp_rec.
    wp_bind (CmpXchg _ _ _).
    iInv (lockN #ℓ) as "[(Hl & HP & Ht)|Hl]" "Hcl".
    - wp_cmpxchg_suc.
      iMod ("Hcl" with "[Hl]") as "_"; first by iRight.
      iModIntro.
      wp_proj.
      wp_if.
      iApply "Hcont".
      by iFrame.
    - wp_cmpxchg_fail.
      iMod ("Hcl" with "[Hl]") as "_"; first by iRight.
      iModIntro.
      wp_proj.
      wp_if.
      iApply ("IH" with "Hcont").
  Qed.

  Lemma release_spec E γ l P :
    nclose (lockN l) ⊆ E →
    {{{ is_lock γ l P ∗ locked γ ∗ P }}} release l @ E {{{ RET #(); True}}}.
  Proof.
    iIntros (HE φ) "(#Hi & Hld & HP) Hcont"; rewrite /release.
    iDestruct "Hi" as (ℓ ->) "Hinv".
    wp_lam.
    iInv (lockN #ℓ) as "[(Hl & HQ & >Ht)|Hl]" "Hcl".
    - iDestruct (own_valid_2 with "Hld Ht") as %Hv. done.
    - wp_store.
      iMod ("Hcl" with "[-Hcont]") as "_"; first by iNext; iLeft; iFrame.
      iApply "Hcont".
      done.
  Qed.

  Global Opaque newlock release acquire.
End lock_spec.

Global Typeclasses Opaque locked.
Global Opaque locked.
Global Typeclasses Opaque is_lock.
Global Opaque is_lock.
