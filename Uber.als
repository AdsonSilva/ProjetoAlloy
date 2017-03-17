module uber 

open util/ordering[Time]

sig Time {}
	
abstract sig Regiao{}

one sig RegiaoLeste, RegiaoOeste, RegiaoNorte, RegiaoSul, RegiaoCentro extends Regiao{}

abstract sig Disponibilidade{}

sig Disponivel extends Disponibilidade{}

sig NaoDisponivel extends Disponibilidade{}

one sig Central {
	carros: set Carro
}

sig Passageiro {
}

sig Placa{}

sig Carro{
	placa: one Placa,
	regiao: one Regiao,
	disponibilidade: set Disponibilidade -> Time 

}

sig Corrida{
	passageiro: set Passageiro -> Time ,
	regiao: set Regiao  -> Time ,
	carro: set Carro -> Time 
}

pred show[]{}

fact disponibilidade{
	#Disponivel = 1
	#NaoDisponivel = 1
	all disponibilidade:Disponibilidade | (disponibilidade in Disponivel) || (disponibilidade in NaoDisponivel)
}

fact placas{
	#Placa = #Carro
	 all p:Placa | one p.~placa
}

fact central{
	#Central = 1
	 all c:Carro| c in Central.carros
}

fact traces{
	init[first]
}

pred init[t:Time]{
	all carro:Carro | carro.(disponibilidade.t) in Disponivel
}

pred temCarroDisponivelNaRegiao[r:Regiao, t:Time]{
	some c:Carro | (c  in Central.carros) and (c.disponibilidade.t) = Disponivel and (c.regiao = r)
}

pred alocarCarro [present, future:Time, p:Passageiro, r:Regiao, corrida:Corrida]{
	(some c:Carro | (c  in Central.carros) and (c.disponibilidade.present) = Disponivel and (c.regiao = r) => 
				(c in corrida.carro.future and c.disponibilidade.future = NaoDisponivel and corrida.passageiro.future = p))

//FAZER TODA A PARTE PARA 'SE NÃO TIVER CARRO DISPONIVEL NA REGIÃO' "acho que vai ser mais fácil"(DRIZIA, HA) 2017


//checar se o carro não está na corrida no tempo anterior
//checar s eo passageiro naõ está na corrida no tempo anterior
//criar um fato para dizer que não existe corrida sem carro e sem passageiro
//REFATORAAAAAAAAR
//FAZER TIPOS DE CARRO
//FAZER O MESMO PRA DESALOCAR

	
}

run show for 9


-- TESTAR

-- Criar uma nova assinatura chamada validaDisponibilidade para verificar se o carro estah disponivel ou nao.
-- tal assinatura serah abstrata. Duas assinaturas irao extender esta, uma serah carroDisponivel e a outra serah carroNaoDisponivel.
-- Criar uma regra para ao inicializar o sistema, a central disponibilizar todos os carros como disponiveis
