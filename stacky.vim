syn clear
syn case match

syn match stkSpecial /{\|}\|\[\|\]\|(\|)\|+\|-\|*\|\/\|@\|#\|$\|^\|&\|=\|:\|;\||/
highlight link stkSpecial Special 

syn match stkStatement /\v<def>|<if>|<if-else>|<for>|<for-all>|<repeat>/
highlight link stkStatement Statement

syn match stkIdentifier /\/\I[^ \t\n]*/
highlight link stkIdentifier Identifier 

syn match stkNumber /\v\d+(\.\d+([eE]\d+)?)?/
highlight link stkNumber Number

syn match stkType /\<[A-Z]\i*\>/
highlight link stkType Type 

syntax keyword stkTodo TODO contained

syn match  stkComment "%.*"                 contains=stkTodo
syn region stkComment start="%("  end=")%"  contains=stkTodo
highlight link stkComment Comment 

syn region stkString start=/"/ skip=/\\"\|\\'/ end=/"/
syn region stkString start=/r"/ skip=/\\"\|\\'/ end=/"/
highlight link stkString String
