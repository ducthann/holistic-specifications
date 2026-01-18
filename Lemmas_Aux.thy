theory Lemmas_Aux
  imports Adaptation
begin 
text \<open>Properties of classical logic \label{appendixproperties} \<close>
lemma aComplement_1: 
  "Assert_wf A M M' \<sigma> \<Longrightarrow> 
    (aAnd A  (aNot A) M M' \<sigma>) = afalse M M' \<sigma>"
  unfolding Assert_wf_def aAnd_def aNot_def afalse_def bopt_def
  by auto

lemma aComplement_2:  
  "Assert_wf A M M' \<sigma> \<Longrightarrow> 
    (aOr A  (aNot A) M M' \<sigma>) = atrue M M' \<sigma>"
  unfolding Assert_wf_def aNot_def aOr_def atrue_def bopt_def 
  by auto

lemma aCommutative_1: 
  "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma> \<rbrakk> \<Longrightarrow> 
    (aOr A  A' M M' \<sigma>) = (aOr A' A M M' \<sigma>)"
  unfolding Assert_wf_def aOr_def bopt_def 
  by auto

lemma aCommutative_2:  
  "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma> \<rbrakk> \<Longrightarrow> 
    (aAnd A A' M M' \<sigma>) = (aAnd A' A M M' \<sigma>)"
  unfolding Assert_wf_def aAnd_def bopt_def 
  by auto

lemma aAssociative_1:  
  "\<lbrakk>Assert_wf A M M' \<sigma>; Assert_wf A' M M' \<sigma> \<rbrakk> \<Longrightarrow> 
   (aOr (aOr A  A') A'' M M' \<sigma>) = (aOr A (aOr A' A'') M M' \<sigma>)"
  unfolding aOr_def bopt_def option.case_eq_if 
  by simp

lemma aAssociative_2:  
  "\<lbrakk>Assert_wf A M M' \<sigma>; Assert_wf A' M M' \<sigma> \<rbrakk> \<Longrightarrow> 
   (aAnd (aAnd A  A') A'' M M' \<sigma>) = (aAnd A (aAnd A' A'') M M' \<sigma>)"
  unfolding aAnd_def bopt_def option.case_eq_if 
  by simp

lemma aDistributive_1:
  "\<lbrakk>Assert_wf A M M' \<sigma>; Assert_wf A' M M' \<sigma>; Assert_wf A'' M M' \<sigma> \<rbrakk> \<Longrightarrow> 
   (aAnd (aOr A  A') A'' M M' \<sigma>) = (aOr (aAnd A A'') (aAnd A' A'') M M' \<sigma>)"
  unfolding aAnd_def aOr_def bopt_def option.case_eq_if 
  by auto

lemma aDistributive_2:
  "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma>; Assert_wf A'' M M' \<sigma> \<rbrakk> \<Longrightarrow> 
   (aOr (aAnd A  A') A'' M M' \<sigma>) = (aAnd (aOr A A'') (aOr A' A'') M M' \<sigma>)"
  unfolding aAnd_def aOr_def bopt_def option.case_eq_if 
  by auto

lemma aDeMorgan_1:  
  "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma> \<rbrakk> \<Longrightarrow> 
    (aNot (aAnd A  A')  M M' \<sigma>) = (aOr (aNot A) (aNot A') M M' \<sigma>)"
  unfolding aAnd_def aOr_def aNot_def bopt_def option.case_eq_if 
  by auto

lemma aDeMorgan_2:  
  "\<lbrakk>Assert_wf A M M' \<sigma>; Assert_wf A' M M' \<sigma> \<rbrakk> \<Longrightarrow> 
    (aNot (aOr A  A') M M' \<sigma>) = (aAnd (aNot A) (aNot A') M M' \<sigma>)"
  unfolding aAnd_def aOr_def aNot_def bopt_def option.case_eq_if 
  by auto
(*text \<open> Here we use higher order abstract syntax (HOAS) to model these, just like HOAS is
   used to model forall and exists in HOL.
   TODO: we need to find out whether this is sufficient to properly express things like
   \<forall>S:SET. ... etc. \<close>
*)(* \<not>(\<exists>x. A) \<equiv> \<forall>x. (\<not> A) *)
lemma aUniversal_existential_1: 
  "Assert_wf A M M' \<sigma> \<Longrightarrow>  
          aNot (aEx (\<lambda>x. A  )) M M' \<sigma> = aAll (\<lambda>x. aNot A) M M' \<sigma>"
  unfolding Assert_wf_def aNot_def aEx_def aAll_def 
  by(auto split: option.splits)
(* \<not>(\<forall>x. A) \<equiv> \<exists>x. (\<not> A) *)
lemma aUniversal_existential_2:  
  "Assert_wf A M M' \<sigma> \<Longrightarrow>  
          aNot (aAll (\<lambda>x. A)) M M' \<sigma> = aEx (\<lambda>x. aNot A) M M' \<sigma>"
  unfolding Assert_wf_def aNot_def aEx_def aAll_def
  using option.case_eq_if option.simps
  by auto
(* (M; M', \<sigma> \<Turnstile> A) \<and> (M; M', \<sigma> \<Turnstile> A \<longrightarrow> A') \<longrightarrow> (M; M', \<sigma> \<Turnstile> A') *)
lemma aImplication:  
  "\<lbrakk>Assert_wf A M M' \<sigma>; Assert_wf A' M M' \<sigma>\<rbrakk>  \<Longrightarrow> 
        (aAnd A (aImp A A'))  M M' \<sigma> = Some True \<Longrightarrow> 
        A' M M' \<sigma> = Some True"
  unfolding Assert_wf_def bopt_def aImp_def aAnd_def aImp_def
  by auto
(* M; M', \<sigma> \<Turnstile> A \<and> \<not> A never holds *)
lemma aNeverHold: 
  "Assert_wf A M M' \<sigma> \<Longrightarrow>  
      (aAnd A (aNot A) M M' \<sigma>) = Some False"
  unfolding Assert_wf_def aAnd_def aNot_def bopt_def
  by auto

text\<open>Some lemmas, which could be useful for reasoning about holistic specifications, are formed and proved in this section.
We make the proof details of these lemmas in Appendix \ref{Lemmas_appendix}.\<close>

lemma object_Unchange_Aux: 
  "M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> \<sigma> = (\<phi>#\<psi>,\<chi>) \<Longrightarrow> 
  \<sigma>' = (\<phi>'#\<psi>',\<chi>') \<Longrightarrow> finite (dom \<chi>) \<Longrightarrow> 
  \<forall>a1.((a1 \<noteq> (this \<phi>) \<and> a1 \<in> dom \<chi> \<and> (this \<phi>) \<in> dom \<chi>)\<longrightarrow> \<chi> a1 = \<chi>' a1)"
proof (induction rule: exec.induct)
  case (exec_method_call \<phi> x y m params stmts a \<chi> C 
                         paramValues M meth \<phi>'' \<psi>)
  thus ?case 
    by simp
next
  case (exec_var_assign \<phi> x y stmts M \<psi> \<chi>)
  thus ?case 
    by simp
next
  case (exec_field_assign \<phi> y x stmts v \<chi> \<chi>' M \<psi>)
  thus ?case 
    by auto
next
  case (exec_new \<phi> x C params stmts 
                  paramValues M c obj' a \<chi> \<chi>' \<psi>) 
  hence "a \<notin> dom \<chi>" 
    by simp 
  thus ?case 
    using exec_new 
    by fastforce
next                              
  case (exec_return \<phi> x stmts \<phi>' x' stmts' M \<psi> \<chi>)
  thus ?case 
    by simp
qed

lemma Changed_FieldAssign_Aux: 
  "M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> \<sigma> = (\<phi>#\<psi>,\<chi>) \<Longrightarrow> 
  \<sigma>' = (\<phi>'#\<psi>',\<chi>') \<Longrightarrow> finite (dom \<chi>) \<Longrightarrow> 
   \<chi>' (this \<phi>) \<noteq> \<chi> (this \<phi>) \<Longrightarrow> (this \<phi>) \<in> dom \<chi> \<Longrightarrow> 
   \<exists>f x. x \<in> dom (vars \<phi>) \<longrightarrow> 
   Some \<chi>' = this_field_update \<phi> \<chi> f (the (vars \<phi> x))" 
proof (induction rule: exec.induct)
  case (exec_method_call \<phi> x y m params stmts a \<chi> C 
                          paramValues M meth \<phi>'' \<psi>)
  thus ?case 
    by simp
next
  case (exec_var_assign \<phi> x y stmts M \<psi> \<chi>)
  thus ?case 
    by simp 
next
  case (exec_field_assign \<phi> y x stmts v \<chi> \<chi>' M \<psi>)
  thus ?case 
    using ident_lookup.elims Pair_inject 
          list.inject option.sel 
    by metis
next
  case (exec_new \<phi> x C params stmts paramValues 
                 M c obj' a \<chi> \<chi>' \<psi>)
  hence "a \<notin> dom \<chi>"  
    by simp
  thus ?case 
    using exec_new 
    by fastforce
next
  case (exec_return \<phi> x stmts \<phi>' x' stmts' M \<psi> \<chi>)
  thus ?case 
    by simp
qed

(* lemmas for adaptation to config and config' *) 
lemma adapt_to_config_Aux:
  "finite (dom (vars \<phi>)) \<Longrightarrow> 
   \<phi>'' = adapt_frame \<phi> \<phi>' \<Longrightarrow> 
   w \<in> dom (vars \<phi>'') \<Longrightarrow> 
   w \<in> dom (vars \<phi>) \<Longrightarrow> 
   (vars \<phi>'' w) = (vars \<phi> w)"
  
  unfolding adapt_frame_def Let_def
  using Frame.select_convs(2) UnCI 
        disjoint_iff_not_equal 
        fresh_idents_empty 
        map_upds_apply_nontin
  by metis

lemma adapt_to_config'_Aux:
  "finite (dom (vars \<phi>)) \<Longrightarrow>  
   \<phi>'' = adapt_frame \<phi> \<phi>' \<Longrightarrow>   
   w \<notin> dom (vars \<phi>) \<Longrightarrow>   
   w \<in> dom (vars \<phi>'')  \<Longrightarrow>  
   \<exists>v. (v \<in> dom (vars \<phi>') \<longrightarrow> 
  (vars \<phi>'' w = vars \<phi>' v) \<and> w \<notin> dom (vars \<phi>'))"

  unfolding adapt_frame_def Let_def
  using Frame.select_convs(2) 
        fresh_nat_is_fresh 
        list.simps(8) 
        map_upds_Nil2 
        sorted_list_of_set.infinite
  by metis

section \<open> Lemmas aiding for Holistic assertions in Isabelle/HOL \label{lemmassupport} \<close>
text\<open> The @{term object_Unchange} is the formalized proof of Lemma \ref{unchangedHeap} in Section \ref{lemmasupport}. \<close>
(* Lemma shows heap unchanged one execution step \<chi>'(a) = \<chi>(a) when a \<noteq> \<phi>(this) \<and> a \<in> dom \<chi> \<and> \<phi>(this) \<in> dom \<chi> *)
lemma object_Unchange: 
  "M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> \<sigma> = (\<phi>#\<psi>,\<chi>) \<Longrightarrow> 
  \<sigma>' = (\<phi>'#\<psi>',\<chi>') \<Longrightarrow> finite (dom \<chi>) \<Longrightarrow> 
  \<forall>a1.((a1 \<noteq> (this \<phi>) \<and> a1 \<in> dom \<chi> \<and> 
    (this \<phi>) \<in> dom \<chi>)\<longrightarrow> \<chi> a1 = \<chi>' a1)" 
  by (simp add: object_Unchange_Aux)

text\<open> The @{term Changed_FieldAssign} is the formalized proof of Lemma \ref{changedfield} in Section \ref{lemmasupport}. \<close>
(* Lemma shows heap is only changed in field_assign update in one execution step
\<chi>'(\<phi>(this)) = field_update (\<chi> (\<phi>(this)), f, \<phi>(x)) when \<chi>'(\<phi>(this)) \<noteq> \<chi>(\<phi>(this)) *)
lemma Changed_FieldAssign: 
  "M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> \<sigma> = (\<phi>#\<psi>,\<chi>) \<Longrightarrow> 
  \<sigma>' = (\<phi>'#\<psi>',\<chi>') \<Longrightarrow> finite (dom \<chi>) \<Longrightarrow> 
   \<chi>' (this \<phi>) \<noteq> \<chi> (this \<phi>) \<Longrightarrow> (this \<phi>) \<in> dom \<chi> \<Longrightarrow> 
   \<exists>f x. x \<in> dom (vars \<phi>) \<longrightarrow> 
    Some \<chi>' = this_field_update \<phi> \<chi> f (the (vars \<phi> x))" 
  using Changed_FieldAssign_Aux by blast

text\<open> Here is a formalized proof of Lemma \ref{adapt1} mentioned in Section \ref{lemmasupport}.\<close>

lemma adapt_to_config:
  "finite (dom (vars \<phi>)) \<Longrightarrow> 
   \<phi>'' = adapt_frame \<phi> \<phi>' \<Longrightarrow> 
   w \<in> dom (vars \<phi>'') \<Longrightarrow> 
   w \<in> dom (vars \<phi>) \<Longrightarrow> 
   (vars \<phi>'' w) = (vars \<phi> w)" 
  using adapt_to_config_Aux by blast

text\<open> Here is a formalized proof of Lemma \ref{adapt2} discussed in Section \ref{lemmasupport}.\<close>

lemma adapt_to_config':  
  "finite (dom (vars \<phi>)) \<Longrightarrow>  
   \<phi>'' = adapt_frame \<phi> \<phi>' \<Longrightarrow>   
   w \<notin> dom (vars \<phi>) \<Longrightarrow>   
   w \<in> dom (vars \<phi>'')  \<Longrightarrow>  
   \<exists>v. (v \<in> dom (vars \<phi>') \<longrightarrow> 
    (vars \<phi>'' w = vars \<phi>' v) \<and> w \<notin> dom (vars \<phi>'))" 
  by (simp add: adapt_to_config'_Aux)

text\<open>Lemma \ref{adapt1adapt2} is also stated as a formalized proof here.\<close>

lemma adapt_to_config_config': 
  "finite (dom (vars \<phi>)) \<Longrightarrow>  
   \<phi>'' = adapt_frame \<phi> \<phi>' \<Longrightarrow> 
   w \<in> dom (vars \<phi>'') \<Longrightarrow> 
  (w \<notin> dom (vars \<phi>) \<and> (\<exists>v. v \<in> dom (vars \<phi>') \<longrightarrow>  
  vars \<phi>'' w =  vars \<phi>' v \<and> w \<notin> dom (vars \<phi>')) \<or> 
  (w \<in> dom (vars \<phi>) \<and> (vars \<phi>'' w = vars \<phi> w)))"  
  using adapt_to_config' adapt_to_config 
  by meson (* text\<open> @{text "P := \<forall> o \<in> S" } \<close>*) 
end