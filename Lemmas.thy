theory Lemmas
  imports Lemmas_Aux
begin 
section \<open> Lemmas aiding for Holistic assertions in Isabelle/HOL \label{lemmassupport} \<close>
text\<open>Some lemmas, which could be useful for reasoning about holistic specifications, are formed and proved in this section.
We make the proof details of these lemmas in Appendix \ref{Lemmas_appendix}.\<close>
(* proof of  (A \<Rightarrow> B) in S  \<equiv> (A in S \<Rightarrow> B in S) *) 
text\<open>The @{term Distrib_In} is the formalized proof of Lemma \ref{Distrib_In} in Section \ref{discusspolicies}. \<close>

lemma Distrib_In: 
  "(aImp (In S A) (In S B) M M' \<sigma>) = 
       (In S(aImp A B)) M M' \<sigma>"
  by (simp add: In_def aImp_def bopt_def option.case_eq_if transConf_def)

text\<open> The @{term not_In} is the formalized proof of Lemma \ref{not_In} in Section \ref{discusspolicies}. \<close> 
(* proof of \<not> (A in S) \<equiv> (\<not> A) in S *) 
(*lemma not_In: 
  "aNot (In S A) M M' \<sigma> = (In S (aNot A)) M M' \<sigma>" 
  by (simp add: not_In_Aux)*)

text\<open> The @{term object_Unchange} is the formalized proof of Lemma \ref{unchangedHeap} in Section \ref{lemmasupport}. \<close>
(* Lemma shows heap unchanged one execution step \<chi>'(a) = \<chi>(a) when a \<noteq> \<phi>(this) \<and> a \<in> dom \<chi> \<and> \<phi>(this) \<in> dom \<chi> *)
lemma object_Unchange: 
  "M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> \<sigma> = (\<phi>#\<psi>,\<chi>) \<Longrightarrow> 
  \<sigma>' = (\<phi>'#\<psi>',\<chi>') \<Longrightarrow> finite (dom \<chi>) \<Longrightarrow> 
  \<forall>a1.((a1 \<noteq> (this \<phi>) \<and> a1 \<in> dom \<chi> \<and> (this \<phi>) \<in> dom \<chi>)\<longrightarrow> \<chi> a1 = \<chi>' a1)" 
  by (simp add: object_Unchange_Aux)

text\<open> The @{term Changed_FieldAssign} is the formalized proof of Lemma \ref{changedfield} in Section \ref{lemmasupport}. \<close>
(* Lemma shows heap is only changed in field_assign update in one execution step
\<chi>'(\<phi>(this)) = field_update (\<chi> (\<phi>(this)), f, \<phi>(x)) when \<chi>'(\<phi>(this)) \<noteq> \<chi>(\<phi>(this)) *)
lemma Changed_FieldAssign: 
  "M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> \<sigma> = (\<phi>#\<psi>,\<chi>) \<Longrightarrow> 
  \<sigma>' = (\<phi>'#\<psi>',\<chi>') \<Longrightarrow> finite (dom \<chi>) \<Longrightarrow> 
   \<chi>' (this \<phi>) \<noteq> \<chi> (this \<phi>) \<Longrightarrow> (this \<phi>) \<in> dom \<chi> \<Longrightarrow> 
   \<exists>f x. x \<in> dom (vars \<phi>) \<longrightarrow> Some \<chi>' = this_field_update \<phi> \<chi> f (the (vars \<phi> x))" 
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
   \<exists>v. (v \<in> dom (vars \<phi>') \<longrightarrow> (vars \<phi>'' w = vars \<phi>' v) \<and> w \<notin> dom (vars \<phi>'))" 
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