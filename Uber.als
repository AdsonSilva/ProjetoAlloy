module uber 

open util/ordering[Time]

sig Time {}
	
abstract sig Regiao{}

one sig RegiaoLeste, RegiaoOeste, RegiaoNorte, RegiaoSul, RegiaoCentro extends Regiao{}

abstract sig validaDisponibilidade{}

sig carroDisponivel extends validaDisponibilidade{}

sig carroNaoDisponivel extends validaDisponibilidade{}

sig Central {
	carros: set Carro
}

sig Passageiro {
	regiao: one Regiao
}

sig Placa{}

sig Carro{
	placa: one Placa,
	regiao: one Regiao,
	validade: one validaDisponibilidade
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


-- TESTAR

-- Criar uma nova assinatura chamada validaDisponibilidade para verificar se o carro estah disponivel ou nao.
-- tal assinatura serah abstrata. Duas assinaturas irao extender esta, uma serah carroDisponivel e a outra serah carroNaoDisponivel.
-- Criar uma regra para ao inicializar o sistema, a central disponibilizar todos os carros como disponiveis
