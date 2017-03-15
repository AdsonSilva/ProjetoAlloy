module uber 

abstract sig Regiao{}

one sig RegiaoLeste, RegiaoOeste, RegiaoNorte, RegiaoSul, RegiaoCentro extends Regiao{}

sig Central {
	carros: set Carro
}

sig Passageiro {
	regiao: one Regiao
}

sig Placa{}

sig Carro{
	placa: one Placa,
	regiao: one Regiao
}

pred show[]{}

fact placas{
	#Placa = #Carro
	 all p:Placa | one p.~placa
}

fact central{
	#Central = 1
	 all c:Carro| c in Central.carros
}

run show for 9
