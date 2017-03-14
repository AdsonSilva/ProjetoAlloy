module uber 

abstract sig Regiao{}

one sig RegiaoLeste, RegiaoOeste, RegiaoNorte, RegiaoSul, RegiaoCentro extends Regiao{}

sig Passageiro {}

sig Placa{}

sig Carro{
	placa: set Placa,
	regiao: one Regiao
}

pred show[]{}

run show for 5
