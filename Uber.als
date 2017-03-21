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
	all c:Carro | all t:Time | one c.disponibilidade.t
}

fact placas{
	#Placa = #Carro
	all p:Placa | one p.~placa
}

fact carro{
	all c:Carro | all t:Time | all corrida:Corrida | c in corrida.carro.t => c.disponibilidade.t = NaoDisponivel	
	all c:Carro | all t:Time | all corrida:Corrida | c !in corrida.carro.t => c.disponibilidade.t = Disponivel
	some c:Carro | some corrida:Corrida | some t: Time | c in corrida.carro.t
	all c:Corrida | all t:Time | lone c.carro.t
}

fact central{
	#Central = 1
	all c:Carro| c in Central.carros
}

fact passageiro{
	all p:Passageiro | all c1, c2:Corrida | all t:Time | (c1 != c2 && p in c1.passageiro.t) => p !in c2.passageiro.t	
	some p:Passageiro | all c:Corrida | some t: Time | p in c.passageiro.t
	some c:Corrida | some t:Time | one c.carro.t
}


fact traces{
	init[first]
}

pred init[t:Time]{
	no Corrida.passageiro.t
	no Corrida.carro.t
	all carro:Carro | carro.(disponibilidade.t) in Disponivel
}

pred temCarroDisponivelNaRegiao[r:Regiao, t:Time]{
	some c:Carro | (c  in Central.carros) and (c.disponibilidade.t) = Disponivel and (c.regiao = r)
}

pred alocarCarro [present, future:Time, p:Passageiro, r:Regiao, corrida:Corrida]{
	(some c:Carro | (c  in Central.carros) and (c.disponibilidade.present) = Disponivel and (c.regiao = r) and p !in (corrida.passageiro.present)=> 
				(c in corrida.carro.future and c.disponibilidade.future in NaoDisponivel and p in corrida.passageiro.future))

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
