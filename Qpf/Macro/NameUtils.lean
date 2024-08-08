open Lean Meta

namespace Lean.Name
/--
  This function has different behaviour from Name.replacePrefix that can be viewed in the following example:

  #eval replacePrefix  `a `b `a.b -- `a
  #eval replacePrefix2 `a `b `a.b -- `b.b

  This comes from the internal declaration of replacePrefix dropping the last named value before continuing
-/
def replacePrefix2 (old_pref new_pref : Name) : Name → Name
  | Name.anonymous => .anonymous
  | Name.str p s   => let p' := if p == old_pref then new_pref
                                else replacePrefix2 old_pref new_pref p
                      Name.mkStr p' s
  | Name.num p v   => let p' := if p == old_pref then new_pref
                                else replacePrefix2 old_pref new_pref p
                      Name.mkNum p' v


def stripPrefix2 (old_pref : Name) : Name → Name
  := Name.replacePrefix2 old_pref .anonymous
end Lean.Name
