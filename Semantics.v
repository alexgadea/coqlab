
(*begin hide*)
Require Import String. Open Scope string_scope.
Require Import Program.

From mathcomp Require Import ssreflect ssrnat ssrbool eqtype fintype.
Import ssreflect ssrnat ssrbool ssrfun eqtype fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Add LoadPath "./" as Top.
Require Import Top.CaseTactic.
Require Import Top.Syntax.

Require Import Vector.
Require Import ZArith.
          
(*end hide*)

(*
  No es suficiente con utilizar el tipo bool de Coq, ya que necesitamos
  dar semántica al "para todo" y el "existe", por lo tanto utilizamos Prop y
  lo renombramos para seguir la notación de la materia.
*)
Notation bool := Prop.

(** *)
(*** Semántica del lenguaje ***)
(** *)

(** *Semántica de los operadores de orden *)
Definition SemOrdOp (op : OrdOp) : Z -> Z -> bool :=
  match op with
  | EqOP => Zeq_bool
  | LeOP => Z.leb
  end
.

(** *Semántica de los operadores booleanos *)
Definition SemBoolOp (op : BoolOp) : bool -> bool -> bool :=
  match op with
  | AndOP => fun a b => a /\ b
  | OrOP =>  fun a b => a \/ b
  end
.

(** *Semántica de los cuantificadores *)
Definition SemQuant (op : QOp) : (Z -> bool) -> bool :=
  match op with
  | ForallOP => fun f => forall (z : Z), f z
  | ExistOP => fun f => exists (z : Z), f z
  end
.

(** *Semántica de los operadores aritmeticos *)
Definition SemZOp (op : ZOp) : Z -> Z -> Z :=
  match op with
  | PlusOP  => Z.add
  | MinusOP => Z.sub
  end
.

Infix "⦃ op '⦄≤'" := (SemOrdOp op) (at level 1).
Infix "⦃ op '⦄∧'" := (SemBoolOp op) (at level 1).
Infix "⦃ op '⦄+'" := (SemZOp op) (at level 1).
Notation "⦃ op '⦄∀'" := (SemQuant op) (at level 1).

(** *Semántica de los entornos *)
(* Dado un entorno E, su semántica será un vector de enteros tamaño E *)
Definition SemEnv (E : Env) := Vector.t Z E.

(* 
   Utilizando la notación de la materia la semántica de un entorno E
   será un subconjunto de Σ tal que los estados están definidos solo
   para las variables de 0 a E; lo denotamos entonces como Σ(E)
*)
Notation "'Σ(' E )" := (SemEnv E) (at level 1, no associativity).

(* Diferentes formas de escribir los estados *)
Notation "[ ]" := (nil _) (format "[ ]").
Notation "z :: σ" := (cons _ z _ σ) (at level 60, right associativity).
Notation "[ x , .. , y ]" := (cons _ x _ .. (cons _ y _ (nil _)) ..).

(** *Semántica de las variables *)
Definition SemVar (E : Env) (v : Var E) : Σ(E) -> Z.
  intros σ.
  apply (@nth_order _ _ σ (var_to_nat v)).
  apply var_to_nat_prop.
Defined.
  
(** *Notation *)
Notation "σ ! v" := (@SemVar _ v σ) (at level 1, no associativity).

(** *Propiedades de los estados *)
(* Utilizando variables con nombre y la notación de la materia este lema es
   equivalente a: 
   [σ | x : z] x = z
*)
Lemma State_Prop_ZVAR : forall (E : Env) (v : Var E) (z : Z) (σ : Σ(E)),
    (z :: σ) ! (ZVAR E) = z.
Proof. auto. Qed.

(* Utilizando variables con nombre y la notación de la materia este lema es
   equivalente a: 
   [σ | x : z] w = σ w
*)
Lemma State_Prop_SVAR : forall (E : Env) (z : Z) (σ : Σ(E)) (w : Var E),
    (z :: σ) ! (SVAR w) = σ ! w.
Proof.
  intros E z σ w.
  dependent destruction w; unfold "_ ! _", nth_order in *; simpl. by auto.
  erewrite -> Fin.of_nat_ext. reflexivity.
Qed.

(* Utilizando variables con nombre y la notación de la materia este lema es
   equivalente a:
   Dado algún conjunto de variables V,
   si para toda w ∈ V, σ w = σ' w
   entonces      
   para toda w ∈ V, [σ | x : z] w = [σ' | x : z] w
*)
Lemma State_Prop_Extension : forall (E : Env) (z : Z) (σ σ' : Σ(E)),
    (forall w : Var E, σ ! w = σ' ! w) ->
    (forall w : Var (succn E), (z :: σ) ! w = (z :: σ') ! w).
Proof.
  intros E z σ σ' H w.
  dependent destruction w.
  + Case "w = ZVAR". by cbn.
  + Case "w = SVAR w".
    unfold "_ ! _", nth_order in *. simpl.
    erewrite -> Fin.of_nat_ext. by apply H.
Qed.

(** *Notation *)
Reserved Notation "⟦ ie '⟧ᵢ'" (at level 1, no associativity).
Reserved Notation "⟦ ae '⟧ₐ'" (at level 1, no associativity).

(** *Semántica de las expresiones enteras *)
Fixpoint SemI E (ie : IntExp E) : Σ(E) -> Z :=
  match ie with
  | VAR v           => fun σ => σ ! v
  | NAT n           => fun _ => Z.of_nat n
  | Neg ie          => fun σ => (- ⟦ ie ⟧ᵢ σ )%Z
  | BNOp zop ie ie' => fun σ => (⟦ ie ⟧ᵢ σ) ⦃zop⦄+ (⟦ ie' ⟧ᵢ σ)
  end
where "⟦ ie '⟧ᵢ'" := (SemI ie).

(** *Semántica de las expresiones booleanas *)
Fixpoint SemA E (ae : Assert E) : Σ(E) -> bool :=
  match ae with
  | BOOL b          => fun σ => b
  | Not ae          => fun σ => ~ (⟦ ae ⟧ₐ σ)
  | OOp oop ie ie'  => fun σ => (⟦ ie ⟧ᵢ σ) ⦃oop⦄≤ (⟦ ie' ⟧ᵢ σ)
  | BBOp bop ae ae' => fun σ => (⟦ ae ⟧ₐ σ) ⦃bop⦄∧ (⟦ ae' ⟧ₐ σ)
  | Quant qop ae    => fun σ => ⦃qop⦄∀ (fun z => ⟦ ae ⟧ₐ (z :: σ))
  end
where "⟦ ae '⟧ₐ'" := (SemA ae).

(** *Propiedades de la semántica denotacional *)
(* 
   Si denotamos a la substitución que substituye cualquier índice i por su
   su sucesor (i+1) como (n ↦ n+1) entonces vale:

             ⟦ ie / (n ↦ n+1) ⟧ᵢ (z :: σ) = ⟦ ie ⟧ᵢ σ

   Notar que la expresión entera "ie / (n ↦ n+1)" que es el resultado de
   aplicarle la substitución a "ie" no tiene índice "0" como variable libre, por
   lo tanto su semántica en un estado extendido que asigna el valor z al índice
   0 es la misma que evaluarla en el estado sin extender.
*)
Lemma Lift_Prop : forall (E : Env) (ie : IntExp E) (z : Z) (σ : Σ(E)),
    ⟦ renI [eta SVAR (E:=E)] ie ⟧ᵢ (z :: σ)
    =
    ⟦ ie ⟧ᵢ σ.
Proof.
  dependent induction ie; intros z' σ.
  + Case "Var".
    simpl. by apply State_Prop_SVAR.
  + Case "Nat". by simpl.
  + Case "Neg". simpl. by rewrite -> IHie.
  + Case "BNOp".
    simpl. rewrite -> IHie1. by rewrite -> IHie2.
Qed.
