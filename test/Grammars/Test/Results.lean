import Grammars.Classes.ContextFree.ClosureProperties.Union
import Grammars.Classes.ContextFree.ClosureProperties.Reverse
import Grammars.Classes.ContextFree.ClosureProperties.Concatenation
import Grammars.Classes.ContextFree.ClosureProperties.Intersection
import Grammars.Classes.ContextFree.ClosureProperties.Complement

import Grammars.Classes.Unrestricted.ClosureProperties.Union
import Grammars.Classes.Unrestricted.ClosureProperties.Reverse
import Grammars.Classes.Unrestricted.ClosureProperties.Concatenation
import Grammars.Classes.Unrestricted.ClosureProperties.Star

import Grammars.Utilities.WrittenByOthers.PrintSorries


section context_free

#check            CF_of_CF_u_CF
#print_sorries_in CF_of_CF_u_CF

#check            CF_of_reverse_CF
#print_sorries_in CF_of_reverse_CF

#check            CF_of_CF_c_CF
#print_sorries_in CF_of_CF_c_CF

#check            nnyCF_of_CF_i_CF
#print_sorries_in nnyCF_of_CF_i_CF

#check            nnyCF_of_complement_CF
#print_sorries_in nnyCF_of_complement_CF

end context_free


section unrestricted

#check            RE_of_RE_u_RE
#print_sorries_in RE_of_RE_u_RE

#check            RE_of_reverse_RE
#print_sorries_in RE_of_reverse_RE

#check            RE_of_RE_c_RE
#print_sorries_in RE_of_RE_c_RE

#check            RE_of_star_RE
#print_sorries_in RE_of_star_RE

end unrestricted
