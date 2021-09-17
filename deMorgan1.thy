theory deMorgan1
  imports Main

begin

lemma de_morgan_1 : "\<not>(p\<or>q) \<longrightarrow> (\<not>p\<and>\<not>q)"
  apply (rule impI)
  apply (rule conjI)
   apply (rule notI)
   apply (erule notE)
    apply (rule disjI1)
    apply assumption
  apply (rule notI)
   apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

end