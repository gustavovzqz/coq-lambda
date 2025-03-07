Import Nat.
Require Import List.
Import ListNotations.
Require Import String.
Require Import Bool.
Open Scope string_scope. 

Create HintDb lambda_db.
From Coq Require Import Setoids.Setoid.

(* ################################################################# 


                         (* SUMÁRIO *)


   1. Definições Básicas 

   2. Definições de Propriedades
      2.1 Possuir tipo T
      2.2 Reduzir para t'

   3. Teorema do Progresso
      3.1 Formas Canônicas
      3.2 Teorema Principal
   
   4. Unicidade

   5. Definição de Função para Extrair o Tipo

   6. Equivalência da Função de Extrair Tipo para a Propriedade (2.1)
      6.1 Funções Auxiliares
      6.2 Teorema Principal

   7. Preservação (incompleto)
      Aqui, dois lemas não foram provados! 


  ################################################################# *)

(*** 1. Definições Básicas *)

Inductive l_type : Type :=
  | LT_nat : l_type
  | LT_bool : l_type
  | LT_arrow : l_type -> l_type -> l_type.


Inductive term : Type :=
  | TM_var : string -> term
  | TM_app : term -> term -> term
  | TM_abs : string -> l_type -> term -> term
  | TM_true : term
  | TM_false : term 
  | TM_nat : nat -> term
  | TM_if : term -> term -> term -> term
  | TM_iszero : term
  | TM_succ : term
  | TM_pred : term.


Inductive value : term -> Prop :=
  | VTrue    : value TM_true
  | VFalse   : value TM_false
  | VAbs     : forall x l t, value (TM_abs x l t)
  | VPred    : value TM_pred
  | VSuc     : value TM_succ
  | V_iszero: value TM_iszero
  | VNat     : forall n, value (TM_nat n).


(* ÚTIL PARA A EXTRAÇÃO *)

Fixpoint nat_to_string (n : nat) : string :=
  match n with
  | O => "0"
  | S m => "S " ++ nat_to_string m
  end.

Fixpoint type_to_string (ty : l_type) : string :=
  match ty with
  | LT_nat => "nat"
  | LT_bool => "bool"
  | LT_arrow ty1 ty2 =>
      let s1 :=
        match ty1 with
        | LT_arrow _ _ => "(" ++ type_to_string ty1 ++ ")"
        | _ => type_to_string ty1
        end in
      let s2 := type_to_string ty2 in
      s1 ++ " -> " ++ s2
  end.

Fixpoint term_to_string (t : term) : string :=
  match t with
  | TM_var x => x
  | TM_app t1 t2 => "(" ++ term_to_string t1 ++ " " ++ term_to_string t2 ++ ")"
  | TM_abs x l t => "("  ++  "fun " ++ x ++ " : " ++ type_to_string l ++ " => " ++ term_to_string t ++ ")"
  | TM_true => "true"
  | TM_false => "false"
  | TM_nat n => nat_to_string n
  | TM_if t1 t2 t3 => "if " ++ term_to_string t1 ++ " then " ++ term_to_string t2 ++ " else " ++ term_to_string t3
  | TM_iszero => "iszero"
  | TM_succ => "succ"
  | TM_pred => "pred"
  end.

(** 1.1 Contexto e substituição *)

Definition context := list (string * l_type).

Fixpoint find s (l : context) :=
  match l with 
  | [] => None
  | (key, h) :: t => if (String.eqb key s) then Some h else 
                      find s t
  end.

Fixpoint subst (x : string) (s : term) (t : term) :=
  match t with 
  | TM_var y => if String.eqb x y then s else t
  | TM_app t1 t2 => TM_app (subst x s t1) (subst x s t2)
  | TM_abs y l t1 => if String.eqb y x then t
                  else TM_abs y l (subst x s t1)
  | TM_true => TM_true
  | TM_false => TM_false
  | TM_iszero => TM_iszero
  | TM_succ => TM_succ
  | TM_pred => TM_pred
  | TM_nat n => TM_nat n
  | TM_if t1 t2 t3 => TM_if (subst x s t1) (subst x s t2) (subst x s t3)
  end.


(* ================================================================= *)

(*** 2. Definição de propriedades de tipagem e computação *)

(** 2.1 Possuir Tipo t *)

Inductive Has_Type : context -> term -> l_type -> Prop :=
  | T_var : forall G x t,
      find x G = Some t ->
      Has_Type G (TM_var x) t

  | T_abs : forall G x t1 A B,
      Has_Type ((x, A) :: G) t1 B ->
      Has_Type G (TM_abs x A t1) (LT_arrow A B)

  | T_app : forall G t1 t2 A B,
      Has_Type G t1 (LT_arrow A B) ->
      Has_Type G t2 A ->
      Has_Type G (TM_app t1 t2) B

  | T_true : forall G,
      Has_Type G TM_true LT_bool

  | T_false : forall G,
      Has_Type G TM_false LT_bool

  | T_is_zero : forall G,
      Has_Type G TM_iszero (LT_arrow LT_nat LT_bool)

  | T_succ : forall G ,
      Has_Type G TM_succ (LT_arrow LT_nat LT_nat)

  | T_pred : forall G, 
      Has_Type G TM_pred (LT_arrow LT_nat LT_nat)

  | T_nat : forall G n, Has_Type G (TM_nat n) LT_nat

  | T_if : forall G t1 t2 t3 A,
      Has_Type G t1 LT_bool ->
      Has_Type G t2 A ->
      Has_Type G t3 A ->
      Has_Type G (TM_if t1 t2 t3) A.


(** 2.2 Reduzir Para *)

Inductive step : term -> term -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
      value v2 ->
      step (TM_app (TM_abs x T2 t1) v2) (subst x v2 t1)

  | ST_App1 : forall t1 t2 t1',
              step t1 t1' ->
              step (TM_app t1 t2) (TM_app t1' t2)

  | ST_App2 : forall t1 t2 t2',
              step t2 t2' ->
              step (TM_app t1 t2) (TM_app t1 t2')

  | ST_AppSucc : forall t1 t1',
                 step t1 t1' ->
                 step (TM_app TM_succ t1) (TM_app TM_succ t1')

  | ST_AppSuccNat : forall n,
                    step (TM_app TM_succ (TM_nat n)) (TM_nat (S n))

  | ST_AppPred : forall t1 t1',
                 step t1 t1' ->
                 step (TM_app TM_pred t1) (TM_app TM_pred t1')

  | ST_AppIsZero: forall t1 t1',
                 step t1 t1' ->
                 step (TM_app TM_iszero t1) (TM_app TM_iszero t1')

  | ST_AppIsZeroTrue : 
                 step (TM_app TM_iszero (TM_nat 0)) (TM_true)

  | ST_AppIsZeroFalse : forall n,
                 step (TM_app TM_iszero (TM_nat (S n))) (TM_false)

  | ST_AppPredNat : forall n,
                    step (TM_app TM_pred (TM_nat n)) (TM_nat (pred n))

  | ST_IfTrue : forall t1 t2,
                step (TM_if TM_true t1 t2) t1

  | ST_IfFalse : forall t1 t2,
                 step (TM_if TM_false t1 t2) t2

  | ST_If : forall t1 t2 t3 t1',
            step t1 t1' ->
            step (TM_if t1 t2 t3) (TM_if t1' t2 t3).


(* Adicionando todos os construtores anteriores ao lambda_db! *)

Hint Constructors l_type : lambda_db.
Hint Constructors value : lambda_db.
Hint Constructors term : lambda_db.
Hint Constructors Has_Type : lambda_db.
Hint Constructors step : lambda_db.


(* Teoremas Gerais para as verificar as definições *)

Example if_true_has_type_nat : forall G,
  Has_Type G (TM_if TM_true (TM_nat 1) (TM_nat 2)) LT_nat.
Proof.
  intros G. auto with lambda_db.
Qed.

Example true_has_type_bool : forall G,
  Has_Type G TM_true LT_bool.
Proof.
  intros G.
  apply T_true.
Qed.

Example nat_five_has_type_nat : forall G,
  Has_Type G (TM_nat 5) LT_nat.
Proof.
  intros G.
  apply T_nat.
Qed.


Example app_abs_to_nat : forall G,
  Has_Type G (TM_app (TM_abs "x" LT_nat (TM_var "x")) (TM_nat 5)) LT_nat.
Proof.
  intros. eauto with lambda_db.
Qed.

Example pred_succ_has_type_nat : forall G,
  Has_Type G (TM_app TM_pred (TM_app TM_succ (TM_nat 2))) LT_nat.
Proof.
  intros G. eauto with lambda_db.
Qed.

(* ================================================================= *)

(*** 3. Teorema do Progresso *)

(** 3.1  Formas Canônicas *)

Lemma bool_canonical : forall t,
  Has_Type [] t LT_bool ->
  value t -> t = TM_true \/ t = TM_false.
Proof.
  intros t H1 H2. destruct H2; try (auto; inversion H1; fail).
Qed.

Lemma nat_canonical : forall t,
  Has_Type [] t LT_nat ->
  value t -> exists n, t = TM_nat n.
Proof.
  intros t H1 H2. destruct H2; try (auto; inversion H1; fail).
  - exists n; reflexivity.
Qed.

Lemma fun_canonical_nat: forall t A,
  Has_Type [] t (LT_arrow A LT_nat) ->
  value t -> t = TM_pred \/ t = TM_succ \/ exists x u, t = TM_abs x A u.
Proof.
  intros t A H1 H2. destruct H2; try (inversion H1; eauto with lambda_db).
Qed.

Lemma fun_canonical_bool: forall t A,
  Has_Type [] t (LT_arrow A LT_bool) ->
  value t -> t = TM_iszero \/ exists x u, t = TM_abs x A u.
Proof.
  intros t A H1 H2. destruct H2; try (inversion H1; eauto with lambda_db).
Qed.

Lemma aux_nat_bool_or_not : forall A, 
  A = LT_nat \/ A = LT_bool \/ (A <> LT_nat /\ A <> LT_bool).
Proof.
  destruct A. 
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. split; intros H; discriminate H.
Qed.

Lemma aux_nat_or_not : forall A,
  A = LT_nat \/ A <> LT_nat.
Proof.
  destruct A.
  - left. reflexivity.
  - right. intros H. discriminate.
  - right. intros H. discriminate.
Qed.

Lemma fun_canonical_not_nat_bool : forall t A B,
  B <> LT_nat /\ B <> LT_bool ->
  Has_Type [] t (LT_arrow A B) ->
  value t -> exists x u, t = TM_abs x A u.
Proof.
  intros t A B H1 H2 H3. destruct H1; destruct H3; (inversion H2; eauto); subst; contradiction.
Qed.

Lemma fun_canonical_not_nat : forall t A B,
  A <> LT_nat  ->
  Has_Type [] t (LT_arrow A B) ->
  value t -> exists x u, t = TM_abs x A u.
Proof.
  intros t A B H1 H2 H3. destruct H3; (inversion H2; eauto); subst; contradiction.
Qed.



(** 3.2 Teorema Principal *)

Theorem progress : forall t T,
  Has_Type [] t T ->
  value t \/ exists t', step t t'.
Proof.
  intros t T H. remember [] as G; induction H; subst; auto with lambda_db.
  - discriminate H.
  - destruct IHHas_Type1; auto.
    (* t1 é um valor *)
    + destruct IHHas_Type2; auto.
      (* t2 é um valor *)

      (* Aqui começa a análise de A e B para a aplicação das formas canônicas *)
         * assert ((B = LT_nat \/ B = LT_bool \/ (B <> LT_nat /\ B <> LT_bool))).
          { eapply aux_nat_bool_or_not. }
          assert (A = LT_nat \/ A <> LT_nat) by apply aux_nat_or_not.
          destruct H3; destruct H4.

          (* B = LT_nat; A = LT_nat*)
        ** subst. apply fun_canonical_nat in H; try assumption. destruct H.
           ++ apply nat_canonical in H0; (try assumption). destruct H0. subst.
              right. eauto with lambda_db.
           ++ destruct H.
              +++ apply nat_canonical in H0; (try assumption). destruct H0. subst.
              right. eauto with lambda_db.
              +++ destruct H. destruct H. right. subst. eauto with lambda_db.
          (* B = LT_nat; A <> LT_nat *)
        ** assert (exists x u, t1 = TM_abs x A u).
           { eapply fun_canonical_not_nat; try (right); eassumption. }
           destruct H5. destruct H5. subst. eauto with lambda_db.
        ** destruct H3.
           (* B = LT_bool, A = LT_nat *)
           ++ subst. apply fun_canonical_bool in H; try assumption.
              apply nat_canonical in H0; try assumption. destruct H0.
              destruct H. 
              +++ destruct x; right; subst; eauto with lambda_db.
              +++ destruct H. destruct H. subst. right. eauto with lambda_db.
            (* B <> LT_nat /\ B <> LT_bool, A = LT_nat *)
           ++ assert (exists x u, t1 = TM_abs x A u).
              { apply fun_canonical_not_nat_bool with B; auto with lambda_db. }
              destruct H5. destruct H5. right. subst. eauto with lambda_db.
              (* A <> LT_nat *)
        ** assert (exists x u, t1 = TM_abs x A u).
           { apply fun_canonical_not_nat with B; assumption. }
           destruct H5. destruct H5. right. subst. eauto with lambda_db.
      (* t2 não é um valor *)
      * destruct H2. right. exists (TM_app t1 x). apply ST_App2, H2.
    (* t1 não é um valor *)
    + destruct H1. right. exists (TM_app x t2). apply ST_App1, H1.
  (* if *)
  - right. destruct IHHas_Type1; auto.
    + destruct (bool_canonical t1); subst; eauto with lambda_db.
    + destruct H2. exists (TM_if x t2 t3). apply ST_If. assumption.
Qed.

(* ================================================================= *)

(*** 4. Unicidade  *)

Theorem unique_types : forall G t T T',
  Has_Type G t T ->
  Has_Type G t T' ->
  T = T'.
Proof.
  intros G t T T' H1. generalize dependent T'. 
  induction H1; intros T' H2; inversion H2; eauto with lambda_db. 
  - subst. symmetry in H. assert (Some t = Some T').
    {  transitivity (find x G); assumption. }
    injection H0. trivial.
  - subst. assert (B = B0). 
    { apply IHHas_Type. assumption. }
    subst. reflexivity.
  - subst. apply IHHas_Type1 in H3. apply IHHas_Type2 in H5. 
    subst. injection H3. trivial.
Qed.



(* ================================================================= *)

(*** 5. Função para computação de tipos *)

Fixpoint eq_l_type (ty1 ty2 : l_type) : bool :=
  match ty1, ty2 with
  | LT_nat, LT_nat => true
  | LT_bool, LT_bool => true
  | LT_arrow ty1a ty1b, LT_arrow ty2a ty2b =>
      eq_l_type ty1a ty2a && eq_l_type ty1b ty2b
  | _, _ => false
  end.


Fixpoint get_type (c : context) (t : term) : option l_type :=
  match t with
  | TM_var x => find x c
  | TM_app t1 t2 =>
      match get_type c t1, get_type c t2 with
      | Some (LT_arrow ty1 ty2), Some ty1' =>
          if eq_l_type ty1 ty1' then Some ty2
          else None
      | _, _ => None
      end
  | TM_abs x l t' => match  (get_type ((x, l) :: c) t') with | Some ty => Some (LT_arrow l ty)
                      | None => None
                     end
  | TM_true => Some LT_bool
  | TM_false => Some LT_bool
  | TM_nat _ => Some LT_nat
  | TM_if t1 t2 t3 =>
      match get_type c t1, get_type c t2, get_type c t3 with
      | Some LT_bool, Some ty2, Some ty3 =>
          if eq_l_type ty2 ty3 then Some ty2
          else None
      | _, _, _ => None
      end
  | TM_iszero => Some (LT_arrow LT_nat LT_bool)
  | TM_succ => Some (LT_arrow LT_nat LT_nat)
  | TM_pred => Some (LT_arrow LT_nat LT_nat)
  end.

Example test_var_in_context : 
  get_type [("x", LT_nat)] (TM_var "x") = Some LT_nat.
Proof. reflexivity. Qed.

Example test_var_not_in_context :
  get_type [] (TM_var "x") = None.
Proof. reflexivity. Qed.

(* ================================================================= *)


(*** 6. A função de computar tipos é equivalente ao Has_Type *)


(** 6.1 Funções auxiliares *)

Lemma eq_l_type_ref : forall A,
  eq_l_type A A = true.
Proof.
  induction A; auto.
  - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
Qed.

Lemma eq_l_type_correct : forall A B,
  eq_l_type A B = true <->
  A = B.
Proof.
  intros A B. split.
  -  generalize dependent B. 
     induction A; destruct B; try (reflexivity || discriminate ).
      + intros H. simpl in H. apply andb_prop in H. destruct H.
        apply IHA1 in H. apply IHA2 in H0. rewrite H. rewrite H0. reflexivity.
  - intros H. rewrite H. apply eq_l_type_ref.
Qed.


Lemma get_type_TM_app : forall G t1 t2 T,
  get_type G (TM_app t1 t2) = Some T ->
  exists A ,
  get_type G t1 = Some (LT_arrow A T) /\
  get_type G t2 = Some A.
Proof.
  intros G t1 t2 T H. simpl in H. 
  destruct (get_type G t1) eqn: E1.
  - destruct l; try discriminate.
    destruct (get_type G t2) eqn: E2; try discriminate.
    destruct (eq_l_type l1 l) eqn: E3; try discriminate.
    rewrite eq_l_type_correct in E3. rewrite E3. exists l.
    injection H as H. rewrite H. split; reflexivity.
  - discriminate H.
Qed.


Lemma get_type_TM_if : forall t1 t2 t3 T G,
  get_type G (TM_if t1 t2 t3) = Some T ->
  get_type G t1 = Some LT_bool /\
  (get_type G t2 = get_type G t3) /\  get_type G t2 = Some T.
Proof. 
  intros t1 t2 t3 T G H. simpl in H. destruct (get_type G t1) eqn:E.
  + destruct l eqn:E1; try discriminate. split; try (reflexivity).
    destruct (get_type G t2) eqn:E2; destruct (get_type G t3) eqn:E3;
    try discriminate. destruct (eq_l_type l0 l1) eqn:E4; try discriminate.
    rewrite eq_l_type_correct in E4. subst. split.
    ++ reflexivity.
    ++ assumption.
  + discriminate.
Qed.



(** 6.2 Teorema principal *)


(* Será que isso é uma outra prova de unicidade? ... *)

Theorem has_type_comp_eqv : forall G t T,
  Has_Type G t T <->
  get_type G t = Some T. Proof.
  intros G t T; split.
  (* -> *)
  - intros H. induction H; eauto with lambda_db.
    + simpl. rewrite IHHas_Type. reflexivity.
    + simpl. rewrite IHHas_Type1. rewrite IHHas_Type2. rewrite eq_l_type_ref.
      reflexivity.
    + simpl. rewrite IHHas_Type1.  rewrite IHHas_Type2. rewrite IHHas_Type3.
      rewrite eq_l_type_ref. reflexivity.
  (* <- *)
  -  generalize dependent T. generalize dependent G. induction t; intros G T H;
    try (simpl in H; injection H as H; rewrite <- H); eauto with lambda_db.
    + apply get_type_TM_app in H. destruct H. destruct H.
         apply IHt1 in H. apply T_app with (x).
         ++ assumption.
         ++ apply IHt2. exact H0. 
    + simpl in H. destruct (get_type ((s, l) :: G) t) eqn :E.
         ++ apply IHt in E. injection H as H. subst.
            apply T_abs, E.
         ++ discriminate H.
    + apply get_type_TM_if in H. destruct H. destruct H0. apply T_if. 
         ++ apply IHt1 in H. assumption.
         ++ apply IHt2 in H1. assumption.
         ++ rewrite H0 in H1. apply IHt3 in H1. assumption.
Qed.

(* ================================================================= *)


(** 7.0 Preservação  *)


Definition included_in l l' := forall k v, 
  find k l = Some v -> find k l' = Some v.

Lemma included_in_add : forall h l l',
  included_in l l' -> included_in (h :: l) (h :: l').
Proof. 
  unfold included_in. intros. simpl. simpl in H0. 
  destruct h. destruct (s =? k).
  - assumption.
  - apply H. assumption.
Qed.




Lemma find_add_twice : forall s h h' G T,
  fst h = fst h' ->
  find s (h :: G) = T <->
  find s (h :: (h' :: G)) = T.
Proof.
  intros. destruct h. destruct h'. split.
  + intros H0. simpl in H. simpl in H0. simpl. destruct (s0 =? s) eqn:E.
    ++ assumption.
    ++ rewrite H in E. rewrite E. assumption.
  + intros H0. simpl in H. simpl in H0. simpl.
    destruct (s1 =? s) eqn:E.
    ++ rewrite String.eqb_eq in E. rewrite E in H. rewrite <- String.eqb_eq in H.
       subst. rewrite H. reflexivity.
    ++ assumption.
Qed.

Lemma find_add_shadows : forall s h h' G T,
  fst h <> fst h' ->
  find s (h :: h' :: G)  =  T <->
  find s (h':: h :: G) = T.
Proof.
  intros. destruct h. destruct h'. simpl in H. split.
  + intros H0. simpl in H0. simpl. destruct (s1 =? s) eqn:E.
    - rewrite String.eqb_eq in E. rewrite E in H. rewrite <- String.eqb_neq in H.
    rewrite H in H0. assumption.
    - assumption.
  + intros H0. simpl in H0. simpl. destruct (s1 =? s) eqn:E.
    - rewrite String.eqb_eq in E. rewrite E in H. rewrite <- String.eqb_neq in H.
      rewrite H. assumption.
    - assumption.
Qed.

Lemma included_in_refl : forall l, 
  included_in l l.
Proof.
  unfold included_in. intros. assumption.
Qed.


Lemma weakening : forall G G' t T,
  included_in G G' ->
  Has_Type G  t T ->
  Has_Type G' t T.
Proof.
  intros. generalize dependent G'. induction H0; eauto with lambda_db; intros.
  assert (included_in ((x, A) :: G) ((x, A) :: G')).
  { apply included_in_add, H. }
  apply T_abs,IHHas_Type, H1.
Qed.

Lemma weakening_empty : forall G t T,
  Has_Type [] t T ->
  Has_Type G t T.
Proof.
  intros. eapply weakening with ([]).
  - unfold included_in. intros;  discriminate.
  - assumption.
Qed.

Hint Resolve find_add_shadows : lambda_db.
Hint Resolve find_add_twice : lambda_db.


(* Os dois teoremas abaixo são simples de verificar que são verdade:

  1. O primeiro diz que se dois elementos para variáveis distintas forem adicionados no contexto,
      então a ordem não faz diferença.

   2. O segundo diz que se dois elementos para uma mesma variável são adicionados no contexto,
   então o segundo sobrescreve o primeiro. 

   O problema é que com o uso de listas como mapas parciais, fica difícil de conseguir uma 
   propriedade indutiva forte o suficiente. *)

Lemma Has_Type_Order : forall t T h h' G,
  fst h <> fst h' ->
  Has_Type (h :: (h':: G)) t T -> 
  Has_Type (h':: (h :: G)) t T.
Proof.
  induction t; intros; inversion H0; eauto with lambda_db.
  - subst. apply T_var. apply find_add_shadows in H3.
    + assumption.
    + admit.
  - subst. apply T_abs. 
    (* preso ... *)
Admitted.

 


Lemma Has_Type_Shadows : forall t T h h' G,
  fst h = fst h' ->
  Has_Type (h :: (h':: G)) t T -> 
  Has_Type (h :: G) t T.
Proof.
  induction t; intros; inversion H0; eauto with lambda_db.
  - apply T_var. simpl. admit.
  - subst. apply T_abs.
    (* Exatamente o mesmo problema que o anterior ... *)
Admitted.


Lemma substitution_aux : forall t Gamma x U  v T ,
   Has_Type ((x, U) :: Gamma) t T ->
   Has_Type [] v U ->
   Has_Type Gamma (subst x v t) T.
Proof.
  induction t; intros;
  inversion H; clear H; subst; simpl; eauto with lambda_db.
    - inversion H3. destruct (x =? s). 
      + injection H1 as H1. subst. apply weakening_empty, H0.
      + apply T_var, H1.
    - destruct (s =? x) eqn:E.
      + apply T_abs. apply Has_Type_Shadows with (x, U).
        ++ simpl. rewrite String.eqb_eq in E. assumption.
        ++ assumption.
      + apply T_abs. apply IHt with (U); try assumption.
        apply Has_Type_Order. 
        ++ rewrite String.eqb_neq in E. simpl. assumption.
        ++ assumption.
Qed.

Theorem preservation: forall t t' T, 
  Has_Type [] t T -> step t t' -> Has_Type [] t' T.
 Proof.
   intros t t' T H H1. generalize dependent T. induction H1; intros; 
   try (inversion H; subst; eauto with lambda_db; fail).
   - inversion H0. subst. inversion H4. subst. eapply substitution_aux; eassumption.
   - inversion H. inversion H3. subst. constructor.
   - inversion H. subst. inversion H3.  constructor.
   - inversion H. inversion H3. subst. constructor.
   - inversion H. subst. inversion H3. subst. constructor.
 Qed.

