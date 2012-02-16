structure Go = 
struct

val () = CoinExec.exec (CommandLine.name (), CommandLine.arguments ())

end
