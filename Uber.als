module uber 

	open util/ordering[Time]

	sig Time {}
	
	one sig Central {
		carros: set Carro
	}

	sig Carro{
		placa: one Placa,
		regiao: one Regiao,
		disponibilidade: set Disponibilidade -> Time 
	}

	sig Passageiro {}

	sig Placa{}

	abstract sig Regiao{}

	one sig RegiaoLeste, RegiaoOeste, RegiaoNorte, RegiaoSul, RegiaoCentro extends Regiao{}

	abstract sig Disponibilidade{}

	sig Disponivel extends Disponibilidade{}

	sig NaoDisponivel extends Disponibilidade{}
	
	sig Corrida{
		passageiro: set Passageiro -> Time ,
		regiao: set Regiao  -> Time ,
		carro: set Carro -> Time 
	}

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


	fact corrida{
		all corrida:Corrida | some t:Time | #corrida.passageiro.t = 1
	}

	/* Execucao Principal.  */
	fact traces{
		init[first]
	}

	/* inicializacao do sistema	*/
	pred init[t:Time]{
		no Corrida.passageiro.t
		no Corrida.carro.t
		all carro:Carro | carro.(disponibilidade.t) in Disponivel
	}

	pred temCarroDisponivelNaRegiao[r:Regiao, t:Time]{
		some c:Carro | (c  in Central.carros) and (c.disponibilidade.t) = Disponivel and (c.regiao = r)
	}

	/*Eh possivel um passageiro solocitar uma corrida para uma determinada regiao - alocando um carro disponivel na central daquela regiao  */
	pred alocarCarro [present, future:Time, p:Passageiro, r:Regiao, corrida:Corrida]{
		(some c:Carro | (c  in Central.carros) and (c.disponibilidade.present) = Disponivel and (c.regiao = r) and p !in (corrida.passageiro.present)=> 
				(c in corrida.carro.future and c.disponibilidade.future in NaoDisponivel and p in corrida.passageiro.future))
		
	 	(some c:Carro | (c  in Central.carros) and (c.disponibilidade.present) = Disponivel and p !in (corrida.passageiro.present)=> 
			(c in corrida.carro.future and c.disponibilidade.future in NaoDisponivel and p in corrida.passageiro.future))

	}

	/*Eh possivel desalocar um carro que nao esta mais sendo usado em uma corrida, ficando assim disponivel na central para uma futura corrida  */
	pred desalocarCarro [present, future:Time, p:Passageiro, r:Regiao, corrida:Corrida]{
		(some c:Carro | (c  in Central.carros) and (c.disponibilidade.present) = NaoDisponivel and p in (corrida.passageiro.present)=> 
				(c !in corrida.carro.future and c.disponibilidade.future in Disponivel and p in corrida.passageiro.future))
	}
    -- Verifica se em toda corrida o carro esta indisponivel
	assert carro_indisponivel_corrida {
		all c:Carro | all t:Time | all corrida:Corrida | c in corrida.carro.t => c.disponibilidade.t = NaoDisponivel	
    }
	-- Verifica se o carro nao está em corrida e ele esta disponivel
	assert carro_disponivel_corrida {
		all c:Carro | all t:Time | all corrida:Corrida | c !in corrida.carro.t => c.disponibilidade.t = Disponivel
    }
	-- Verifica se toda corrida tem pelo um passageiro
	assert toda_corrida_tem_passageiro {
		all corrida:Corrida | some t:Time | #corrida.passageiro.t = 1
	}
    -- Verifica se todas as corridas estão em uma região
	assert toda_corrida_em_regiao {
    	all corrida:Corrida | all t:Time | corrida.regiao.t in Regiao 
   }
	
	pred show[]{}

	check carro_indisponivel_corrida for 	9	
	check carro_disponivel_corrida for 	9	
	check toda_corrida_tem_passageiro for 9
	check toda_corrida_em_regiao for 9

	run show for 9
