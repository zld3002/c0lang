structure Go = 
struct

val () = CoinExec.go (CommandLine.name (), CommandLine.arguments ())

end
