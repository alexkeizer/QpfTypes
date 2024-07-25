open Lean Meta

namespace Lean.Name
-- This function has diffreent behaviour from Name.replacePrefix
def replacePrefix2 (old_pref new_pref : Name) : Name → Name
  | Name.anonymous => Name.anonymous
  | Name.str p s   => let p' := if p == old_pref then new_pref
                                else replacePrefix2 old_pref new_pref p
                      Name.mkStr p' s
  | Name.num p v   => let p' := if p == old_pref then new_pref
                                else replacePrefix2 old_pref new_pref p
                      Name.mkNum p' v


def stripPrefix2 (old_pref : Name) : Name → Name
  := Name.replacePrefix2 old_pref .anonymous
end Lean.Name
