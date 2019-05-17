
(** Variables *)
(** @see: Benton's strongly typed representation of variabels. 
http://research.microsoft.com/en-us/um/people/nick/typedsyntax.pdf *)

(*begin hide*)
Add LoadPath "./" as Top.
Require Import Top.CaseTactic.
Require Import String. Open Scope string_scope.

From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq fintype.
Import ssreflect ssrnat ssrbool ssrfun eqtype seq fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Program.
(*end hide*)      
(** *)
(*** Sintaxis del lenguaje ***)
(** *)

Inductive OrdOp := EqOP | LeOP.

Inductive BoolOp := AndOP | OrOP.

Inductive ZOp := PlusOP | MinusOP.

Inductive QOp := ForallOP | ExistOP.

(** *Un entorno será un número natural *)
(* 
   Básicamente un entorno nos define el natural n tal que caracteriza 
   el conjunto de variables libres.
*)
Definition Env := nat.

(* Definición de los índices/variables *)
Inductive Var : Env -> Type :=
| ZVAR : forall E, Var (S E)
| SVAR : forall E, Var E -> Var (S E)
.

Fixpoint var_to_nat (E : Env) (v : Var E) : nat :=
  match v with
  | ZVAR _ => O
  | SVAR _ v' => S (var_to_nat v')
  end.

Lemma var_to_nat_S : forall (E : Env) (v : Var E),
    var_to_nat (SVAR v) = succn (var_to_nat v).
Proof.
    by auto.
Qed.

Hint Rewrite var_to_nat_S : SimplVar.

(* 
   Para todo índice i con tipo Var n, el resultado de traducir el índice a
   nat es menor estricto que n.
 *)
Fixpoint var_to_nat_prop (E : Env) (v : Var E) : (var_to_nat v < E)%coq_nat
  := match v with
    | ZVAR E' => (PeanoNat.Nat.lt_0_succ E')
    | SVAR E' v' => Lt.lt_n_S (var_to_nat v') E' (var_to_nat_prop v')
    end.

(** *Sintaxis de la expresiones enteras *)
Inductive IntExp (E : Env) : Type :=
| VAR  : Var E    -> IntExp E
| NAT  : nat        -> IntExp E
| Neg  : IntExp E -> IntExp E
| BNOp : ZOp    -> IntExp E -> IntExp E -> IntExp E
.

(** *Sintaxis de la expresiones booleanas *)
Inductive Assert (E : Env) : Type :=
| BOOL  : bool       -> Assert E
| Not   : Assert E -> Assert E
| OOp   : OrdOp    -> IntExp E    -> IntExp E -> Assert E
| BBOp  : BoolOp   -> Assert E    -> Assert E -> Assert E
| Quant : QOp      -> Assert E.+1 -> Assert E
.
Arguments BOOL [E] _.
Arguments NAT [E] _.

(** *Notation *)
Notation "⌈ b ⌉" := (BOOL b) (at level 1, no associativity).
Notation "⌊ n ⌋" := (NAT n) (at level 1, no associativity).
Notation "⎨ v ⎬" := (VAR v) (at level 202, no associativity).

(*begin hide*)
(** *MAP Section *)
Section MAP.

  Variable P : Env -> Type.
  Definition Map E E' := Var E -> P E'.
  
  (* Head, tail and cons *)
  Definition tlMap E E' (m:Map (E.+1) E') : Map E E' := fun v => m (SVAR v).
  Definition hdMap E E' (m:Map (E.+1) E') : P E' := m (ZVAR _).
  
  Definition consMap E E' (hd: P E') (tl : Map E E') : Map (E.+1) E' :=
    (fun var =>
       match var in Var p return (Map (p.-1) E') -> P E' with 
       | ZVAR _ => fun _ => hd
       | SVAR _ var' => fun tl' => tl' var'
       end tl). 
  
  Axiom MapExtensional : forall E E' (r1 r2 : Map E E'),
      (forall var, r1 var = r2 var) -> r1 = r2.
  
  Lemma hdConsMap : forall E E' (v : P E') (s : Map E E'), hdMap (consMap v s) = v. 
  Proof. by []. Qed.
  Lemma tlConsMap : forall E E' (v : P E') (s : Map E E'), tlMap (consMap v s) = s. 
  Proof. move => E E' v s. by apply MapExtensional. Qed.

  Import Program.
  Lemma consMapEta : forall E E' (m:Map (E.+1) E'), m = consMap (hdMap m) (tlMap m).
  Proof. move => E E' m. apply MapExtensional.
         intro. by dependent destruction var. 
  Qed.
  
  (*==========================================================================
    Package of operations used with a Map
      vr maps a Var into Var or Value (so is either the identity or TVAR)
      vl maps a Var or Value to a Value (so is either TVAR or the identity)
      wk weakens a Var or Value (so is either SVAR or renaming through SVAR on 
      a value)
    ==========================================================================*)
  Record MapOps :=
    {
      vr : forall E, Var E -> P E;   
      vl : forall E, P E -> IntExp E;
      wk : forall E, P E -> P (E.+1);
      wkvr : forall E (var : Var E), wk (vr var) = vr (SVAR var);
      vlvr : forall E (var : Var E), vl (vr var) = VAR var
    }.
  Variable ops : MapOps.
  
  Definition lift E E' (m : Map E E') : Map (E.+1) (E'.+1) :=
    (fun var => match var in Var p return Map (p.-1) E' -> P (E'.+1) with
             | ZVAR _ => fun _ => vr ops (ZVAR _)
             | SVAR _ x => fun m => wk ops (m x)
             end m).
  
  Definition shiftMap E E' (m : Map E E') : Map E (E'.+1) :=
    fun var => wk ops (m var).
  Definition idMap E : Map E E := fun (var : Var E) => vr ops var.
  
  Lemma shiftConsMap :
    forall E E' (m : Map E E') (x : P E'),
    shiftMap (consMap x m) = consMap (wk ops x) (shiftMap m). 
  Proof. intros E E' m x. apply MapExtensional. by dependent destruction var. Qed.
  
  Lemma LiftMapDef :
    forall E E' (m : Map E' E), lift m = consMap (vr ops (ZVAR _)) (shiftMap m).
  Proof. intros. apply MapExtensional. by dependent destruction var. Qed.
  
  Fixpoint travI {E E'} (ie : IntExp E) (m : Map E E') : IntExp E' :=
    match ie with
    | VAR v   => vl ops (m v)
    | NAT n   => NAT n
    | Neg ie  => Neg (travI ie m)
    | BNOp nop ie ie' => BNOp nop (travI ie m) (travI ie' m)
    end
  .
  Fixpoint travA {E E'} (ae : Assert E) : Map E E' -> Assert E' :=
    match ae with
    | BOOL b          => fun m => BOOL b
    | Not ae          => fun m => Not (travA ae m)
    | OOp oop ie ie'  => fun m => OOp oop (travI ie m) (travI ie' m)
    | BBOp bop ae ae' => fun m => BBOp bop (travA ae m) (travA ae' m)
    | Quant qop ae    => fun m => Quant qop (travA ae (lift m))
    end.
  
  Definition mapI E E' m v := @travI E E' v m.
  Definition mapA E E' m e := @travA E E' e m.
  
  Variable E E' : Env.
  Variable m : Map E E'.

  Lemma mapBOOL : forall (b : bool), mapA m (BOOL b) = BOOL b.
  Proof.
    intro. unfold mapA. unfold travA. destruct E. reflexivity. reflexivity.
  Qed.

  Lemma mapNAT : forall (n : nat), mapI m (NAT n) = NAT n.
  Proof.
    intro. unfold mapI. unfold travI. destruct E. reflexivity. reflexivity.
  Qed.
  
  Lemma mapVAR : forall (var : Var _),
      mapI m (VAR var) = vl ops (m var).
  Proof.
    intro. unfold mapI. by unfold travI.
  Qed.
  
  Lemma mapNEG : forall (ie : IntExp _),
      mapI m (Neg ie) = Neg (mapI m ie).
  Proof.
    intros e. unfold mapI. by simpl.
  Qed.

  Lemma mapNOT : forall (ae : Assert _),
      mapA m (Not ae) = Not (mapA m ae).
  Proof.
    intros e. unfold mapA. by simpl.
  Qed.

  Lemma mapOOp : forall op e1 e2,
      mapA m (OOp op e1 e2) = OOp op (mapI m e1) (mapI m e2).
  Proof.
    intros. unfold mapI. unfold travI. destruct E. reflexivity. reflexivity.
  Qed.
  
  Lemma mapBOp : forall op e1 e2,
      mapA m (BBOp op e1 e2) = BBOp op (mapA m e1) (mapA m e2).
  Proof.
    intros. unfold mapA. unfold travA. destruct E. reflexivity. reflexivity.
  Qed.

  Lemma mapNOp : forall op e1 e2,
      mapI m (BNOp op e1 e2) = BNOp op (mapI m e1) (mapI m e2).
  Proof.
    intros. unfold mapI. unfold travI. destruct E. reflexivity. reflexivity.
  Qed.
  
  Lemma mapQUANT : forall qop (ae : Assert _),
      mapA m (Quant qop ae) = Quant qop (mapA (lift m) ae).
  Proof.
    intro. unfold mapA. unfold travA. destruct E. reflexivity. reflexivity.
  Qed.
  
  Lemma liftIdMap : lift (@idMap E) = @idMap (E.+1).
  Proof.
    apply MapExtensional. dependent destruction var; [by [] | by apply wkvr].  
  Qed.
  
  Lemma idMapDef :
    @idMap (E.+1) = consMap (vr ops (ZVAR _)) (shiftMap (@idMap E)).
  Proof.
    apply MapExtensional. dependent destruction var; first by [].
    unfold idMap, shiftMap. simpl. by rewrite wkvr.
  Qed.

End MAP.
  
Hint
  Rewrite
  mapVAR mapBOOL mapNAT mapNOT mapNEG mapNOp mapBOp mapOOp mapQUANT : mapHints.

Require Import String. Open Scope string_scope.

Arguments idMap [P] _ _ _.

Lemma applyIdMapIntExp : forall P (ops:MapOps P) E,
    (forall (ie : IntExp E), mapI ops (idMap ops E) ie = ie).
Proof.
  intros P ops.
  induction ie.
  + Case "ie = VAR ...".
    rewrite -> mapVAR.
    apply vlvr.
  + Case "ie = NAT ...". by rewrite -> mapNAT.
  + Case "ie = NEG ...".
    rewrite -> mapNEG. by rewrite -> IHie.
  + Case "ie = BNOP ie ie'".
    rewrite -> mapNOp.
    rewrite -> IHie1. by rewrite -> IHie2.
Qed.

Lemma applyIdMapAssert : forall P (ops:MapOps P) E,
    (forall (ae : Assert E), mapA ops (idMap ops E) ae = ae).
Proof.
  intros P ops.
  induction ae.
  + Case "ae = BOOL ...". by rewrite -> mapBOOL.
  + Case "ie = NOT ...".
    rewrite -> mapNOT. by rewrite -> IHae.
  + Case "ae = OOP ie ie'".
    rewrite -> mapOOp. by do 2 rewrite -> applyIdMapIntExp.
  + Case "ae = BBOP ae ae'".
    rewrite -> mapBOp.
    rewrite -> IHae1. by rewrite -> IHae2.
  + Case "ae = Quant ae".
    rewrite -> mapQUANT.
    rewrite -> liftIdMap.
      by rewrite -> IHae.
Qed.

(** *RENAMING Section *)
Definition Ren := Map Var.

(** update for 8.4 *)
Definition RenMapOps := (@Build_MapOps _ (fun _ v => v)
                                      VAR SVAR
                                      (fun _ _ => Logic.eq_refl)
                                      (fun _ _ => Logic.eq_refl)
                       ).

Definition renI := mapI RenMapOps.
Definition renA := mapA RenMapOps.
Definition liftRen := lift RenMapOps.
Definition shiftRen := shiftMap RenMapOps.
Definition idRen := idMap RenMapOps.
Arguments idRen : clear implicits.

(*==========================================================================
  Composition of renaming
  ==========================================================================*)

Definition composeRen P E E' E''
           (m : Map P E' E'') (r : Ren E E') : Map P E E''
  := fun var => m (r var). 

Lemma liftComposeRen : forall P ops E E' E''
                         (m:Map P E' E'') (r:Ren E E'),
    lift ops (composeRen m r) = composeRen (lift ops m) (liftRen r).
Proof. intros. apply MapExtensional. by dependent destruction var. Qed.

Lemma applyComposeRenIntExp : forall (E : Env),
    (forall (ie : IntExp E) P ops E' E'' (m:Map P E' E'') (s : Ren E E'),
        mapI ops (composeRen m s) ie = mapI ops m (renI s ie)).
Proof.
  induction ie.
  + Case "ie = VAR".
    intros P ops E' E'' m s.
    rewrite -> mapVAR.
    unfold renI. repeat (rewrite -> mapVAR). by unfold composeRen.
  + SCase "ie = NAT".      
    intros P ops E' E'' m s.
    unfold renI. by repeat (rewrite -> mapNAT).
  + SCase "ie = NEG".
    intros P ops E' E'' m s. unfold renI.
    repeat (rewrite -> mapNEG). by rewrite -> IHie.
  + Case "ie = BNOp op e1 e2".
    intros P ops E' E'' m s. unfold renI.
    repeat (rewrite -> mapNOp). rewrite -> IHie1. by rewrite -> IHie2.
Qed.
    
Lemma applyComposeRenAssert : forall (E : Env),
    (forall (ae : Assert E) P ops E' E'' (m:Map P E' E'') (s : Ren E E'),
        mapA ops (composeRen m s) ae = mapA ops m (renA s ae)).
Proof.
  induction ae.
  + SCase "ae = BOOL".
    intros P ops E' E'' m s.
    unfold renA. by repeat (rewrite -> mapBOOL).
  + SCase "ae = NOT".
    intros P ops E' E'' m s. unfold renA.
    repeat (rewrite -> mapNOT). by rewrite -> IHae.
  + Case "ae = OOp op e1 e2".
    intros P ops E' E'' m s. unfold renA.
    repeat (rewrite -> mapOOp). by do 2 rewrite -> applyComposeRenIntExp.
  + Case "ae = BBOp op e1 e2".
    intros P ops E' E'' m s. unfold renA.
    repeat (rewrite -> mapBOp). rewrite -> IHae1. by rewrite -> IHae2.
  + SCase "ae = Quant e1".
    intros P ops E' E'' m s. unfold renA.
    repeat (rewrite -> mapQUANT). rewrite -> liftComposeRen. by rewrite -> IHae.
Qed.

(** *Substitution Section *)
Definition Sub := Map IntExp.
Definition Δ := Sub.
(** update for 8.4 *)

Definition SubMapOps : MapOps IntExp :=
  (@Build_MapOps _ VAR (fun _ v => v)
                 (fun E => renI (fun v => SVAR v))
                 (fun _ _ => Logic.eq_refl)
                 (fun _ _ => Logic.eq_refl)
  ).

Definition subI := mapI SubMapOps.
Definition subA := mapA SubMapOps.
Definition shiftSub := shiftMap SubMapOps.
Definition liftSub := lift SubMapOps.
Definition idSub := idMap SubMapOps.
Arguments idSub : clear implicits.

(** *Notation *)
Notation "[ x , .. , y ]" :=
  (consMap x .. (consMap y (idSub _)) ..) : Sub_scope.
Delimit Scope Sub_scope with subst.
Arguments subI _ _ _%Sub_scope _.
Arguments subA _ _ _%Sub_scope _.

Notation "ie '⫽ᵢ' δ" := (@subI _ _ δ ie) (at level 1, no associativity).
Notation "ae '⫽ₐ' δ" := (@subA _ _ δ ae) (at level 1, no associativity).

Ltac UnfoldRenSub := (unfold subI; unfold subA; unfold renI;
                     unfold renA; unfold liftSub; unfold liftRen
                    ).
Ltac FoldRenSub := (fold subI; fold subA; fold renI; fold renA;
                   fold liftSub; fold liftRen
                  ).
Ltac SimplMap := (UnfoldRenSub; autorewrite with mapHints; FoldRenSub).

(*==========================================================================
  Composition of substitution followed by renaming
  ==========================================================================*)

Definition composeRenSub E E' E'' (r : Ren E' E'') (s : Sub E E') : Sub E E'' :=
  fun var => renI r (s var)
.

Lemma liftComposeRenSub : forall E E' E'' (r:Ren E' E'') (s:Sub E E'),
    liftSub (composeRenSub r s) = composeRenSub (liftRen r) (liftSub s).
Proof.
  intros. apply MapExtensional. dependent destruction var; first by [].
  simpl. unfold composeRenSub. unfold liftSub. unfold renI at 1.
  rewrite <- applyComposeRenIntExp. unfold lift. simpl wk. unfold renI.
  rewrite <- applyComposeRenIntExp. reflexivity.
Qed.

Lemma applyComposeRenSubIntExp : forall (E : Env),
    (forall (ie : IntExp E) E' E'' (r : Ren E' E'') (s : Sub E E'),
        subI (composeRenSub r s) ie = renI r (subI s ie)).
Proof.
  induction ie.
  + Case "ie = VAR".
    intros E' E'' r s.
      by SimplMap.
  + Case "ie = NAT".      
    intros E' E'' r s.
      by SimplMap.
  + Case "ie = NEG".
    intros E' E'' r s. unfold "_ ⫽ᵢ _".
    rewrite -> mapNEG. by rewrite -> IHie.
  + Case "ie = BNOP".
    intros E' E'' r s. unfold "_ ⫽ᵢ _".
    do 2 rewrite -> mapNOp. rewrite -> IHie1. by rewrite -> IHie2.
Qed.

Lemma applyComposeRenSubAssert : forall (E : Env),
    (forall (ae : Assert E) E' E'' (r : Ren E' E'') (s : Sub E E'),
        subA (composeRenSub r s) ae = renA r (subA s ae)).
Proof.
  induction ae.
  + Case "ae = BOOL".      
    intros E' E'' r s.
      by SimplMap.
  + Case "ae = NOT".
    intros E' E'' r s. unfold "_ ⫽ₐ _".
    rewrite -> mapNOT. by rewrite -> IHae.
  + Case "ie = OOP".
    intros E' E'' r s. unfold "_ ⫽ₐ _".
    do 2 rewrite -> mapOOp. by do 2 rewrite -> applyComposeRenSubIntExp.
  + Case "ie = BBOP".
    intros E' E'' r s. unfold "_ ⫽ₐ _".
    do 2 rewrite -> mapBOp. rewrite -> IHae1. by rewrite -> IHae2.
  + Case "ie = QUANT".
    intros E' E'' r s. unfold "_ ⫽ₐ _".
    rewrite -> mapQUANT. rewrite -> liftComposeRenSub. by rewrite -> IHae.
Qed.

(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Definition composeSub E E' E'' (s' : Sub E' E'') (s : Sub E E') : Sub E E''
  := fun var => subI s' (s var).
Arguments composeSub _ _ _ _%Sub_scope _%Sub_scope _.

Lemma liftComposeSub : forall E E' E'' (s' : Sub E' E'') (s : Sub E E'),
    liftSub (composeSub s' s) = composeSub (liftSub s') (liftSub s).
  intros. apply MapExtensional. dependent destruction var; first by []. 
  unfold composeSub. simpl liftSub.
  rewrite <- applyComposeRenSubIntExp. unfold composeRenSub. unfold subI.
    by rewrite <- applyComposeRenIntExp.
Qed.

Lemma substComposeSubIntExp : forall (E : Env),
    (forall (ie : IntExp E) E' E'' (s' : Sub E' E'') (s : Sub E E'),
        subI (composeSub s' s) ie = subI s' (subI s ie)).
Proof.
  induction ie.
  + Case "ie = VAR". intros  E' E'' s' s. unfold "_ ⫽ᵢ _".
      by repeat (rewrite -> mapVAR).
  + Case "ie = NAT". intros E' E'' s' s. unfold "_ ⫽ᵢ _".
      by repeat (rewrite -> mapNAT).
  + Case "ie = NEG". intros E' E'' s' s. unfold "_ ⫽ᵢ _".
    rewrite -> mapNEG. by rewrite -> IHie.
  + Case "ie = BNOP". intros E' E'' s' s. unfold "_ ⫽ᵢ _".
    do 2 rewrite -> mapNOp. rewrite -> IHie1. by rewrite -> IHie2.
Qed.

Lemma substComposeSubAssert : forall (E : Env),
    (forall (ae : Assert E) E' E'' (s' : Sub E' E'') (s : Sub E E'),
        subA (composeSub s' s) ae = subA s' (subA s ae)).
Proof.
  induction ae.
  + Case "ae = BOOL". intros E' E'' s' s. unfold "_ ⫽ₐ _".
      by repeat (rewrite -> mapBOOL).
  + Case "ae = NOT". intros E' E'' s' s. unfold "_ ⫽ₐ _".
    rewrite -> mapNOT. by rewrite -> IHae.
  + Case "ae = OOP". intros E' E'' s' s. unfold "_ ⫽ₐ _".
    do 2 rewrite -> mapOOp. by do 2 rewrite -> substComposeSubIntExp.
  + Case "ae = BOP". intros E' E'' s' s. unfold "_ ⫽ₐ _".
    do 2 rewrite -> mapBOp. rewrite -> IHae1. by rewrite -> IHae2.
  + SCase "ae = QUANT". intros E' E'' s' s. unfold "_ ⫽ₐ _".
    rewrite -> mapQUANT. rewrite -> liftComposeSub.
      by rewrite -> IHae.
Qed.

(** updated for 8.4 *)
Lemma composeCons : forall E E' E'' (s':Sub E' E'') (s:Sub E E') (v:IntExp _), 
    composeSub (consMap v s') (liftSub s) = consMap v (composeSub s' s).
  intros. apply MapExtensional. dependent destruction var; first by [].
  unfold composeSub. simpl consMap. unfold subI. unfold liftSub.
  unfold lift. simpl wk. rewrite <- applyComposeRenIntExp.
  unfold composeRen. auto.
Qed.

Lemma composeSubIdLeft : forall E E' (s : Sub E E'), composeSub (idSub _) s = s.
Proof. intros. apply MapExtensional.  intros var.
       apply applyIdMapIntExp.
Qed.

Lemma composeSubIdRight : forall E E' (s:Sub E E'), composeSub s (idSub _) = s.
Proof.
  destruct E. by []. by [].
Qed.

(*end hide*)
