package model;

import java.util.ArrayList;
import java.util.EmptyStackException;
import java.util.Stack;

import exception.CartaNotFoundException;
import exception.PilhaVaziaException;
import util.Carta;
import util.Naipe;

/**Representa uma pilha do jogo Paciência. 
 * Pode receber cartas segundo as regras para cada tipo de Pilha.*/
public abstract class Pilha {
	
	/**Pilha de cartas*/
	protected /*@ spec_public @*/ Stack<Carta> cartas;
	
	/*@ assignable this.cartas;
	  @ ensures    this.cartas != null;
	  @*/
	public Pilha() {
		this.cartas = new Stack<>();
	}
	
	/**Cada Pilha implementa seu modo de verificar se pode receber uma carta.
	 * @return Booleano representando se a carta pode ser inserida ou não*/
	protected /*@ spec_public @*/ abstract /*@ pure @*/ boolean verificarCarta(Carta carta);
	
	/**Inserir carta na pilha.*/
	/*@ requires   carta != null; 
	  @ assignable this.cartas;
	  @ ensures    this.cartas.size() == \old(this.cartas.size()) + 1;
	  @ ensures    this.cartas.search(carta) != -1;
	  @*/
	public void inserirCarta(Carta carta) {
		cartas.push(carta);
	}
	
	/**Inserir cartas na pilha.*/
	/*@ requires   cartas.contains(null) == false; 
	  @ assignable this.cartas;
	  @ ensures    this.cartas.size() == \old(this.cartas.size()) + cartas.size();
	  @ ensures    this.cartas.containsAll(cartas) == true;
	  @*/
	public void inserirCartas (ArrayList<Carta> cartas) {
		this.cartas.addAll(cartas);
	}
	
	/**Recebe uma carta para ser colocada ou não na pilha. 
	 * Depende da verificação de cada tipo de Pilha.
	 * @param carta		Carta que quer ser inserida
	 * @return Booleano representando se a carta foi inserida*/
	/*@ 	requires   carta != null && this.verificarCarta(carta); 
	  @ 	assignable this.cartas;
	  @ 	ensures    this.cartas.size() == \old(this.cartas.size()) + 1;
	  @ 	ensures    this.cartas.search(carta) != -1;
	  @ also
	  @ 	requires   carta == null || this.verificarCarta(carta) == false;
	  @ 	ensures    this.cartas == \old(this.cartas);
	  @*/
	public boolean receberCarta(Carta carta) {
		if (carta != null && verificarCarta(carta)) {
			inserirCarta(carta);
			return true;
		}
		return false;
	}
	
	/**Recebe uma coleção de cartas para serem colocadas ou não na pilha. 
	 * Depende da verificação de cada tipo de Pilha.
	 * @param cartas		Cartsa que querem ser inseridas
	 * @return Booleano representando se as cartas foram inseridas*/
	/*@ 	requires   cartas.contains(null) == false;
	  @ 	assignable this.cartas;
	  @ also
	  @ 	requires   cartas == null || cartas.size() <= 0;
	  @ 	assignable this.cartas;
	  @ 	ensures    this.cartas == \old(this.cartas);
	  @*/
	public boolean receberCartas(ArrayList<Carta> cartas) {
		
		if (cartas == null || cartas.size() <= 0 ) return false;
		
		for (int i = 0; i < cartas.size(); i++){
			if (verificarCarta(cartas.get(i))) {
				inserirCarta(cartas.get(i));
			}else {
				while (i-- > 0) puxarCartaTopo();
				return false;
			}
		}
		return true;
	}
	
	
	/**Carta do topo da pilha.
	 * @return Carta do topo da pilha*/
	/*@   public normal_behavior
	  @     requires     cartas.isEmpty();
	  @ also
	  @   public exceptional_behavior
	  @ 	requires     !cartas.isEmpty();
	  @ 	signals_only PilhaVaziaException;
	  @*/
	public Carta cartaTopo() throws PilhaVaziaException {
		Carta carta = new Carta (1, Naipe.COPAS);
		try {
			carta = cartas.peek();
		} catch (EmptyStackException e) {
			throw new PilhaVaziaException("Não há carta no topo, pilha vazia");
		}
		
		return carta;
	}

	
	/**Retirar carta do topo da pilha.
	 * @return Carta do topo da pilha*/
	/*@   public normal_behavior
	  @	   requires   !cartas.isEmpty();
	  @    assignable this.cartas;
	  @    ensures    this.cartas.size() == \old(this.cartas.size()) - 1;
	  @    ensures    this.cartas.search(this.cartas.peek()) == -1;
	  @ also
	  @   public exceptional_behavior
	  @ 	requires     !cartas.isEmpty();
	  @ 	signals_only PilhaVaziaException;
	  @*/
	public Carta puxarCartaTopo() throws PilhaVaziaException{
		Carta carta = new Carta (1, Naipe.COPAS);
		try {
			carta = cartas.pop();
		} catch (EmptyStackException e) {
			throw new PilhaVaziaException("Não há carta no topo, pilha vazia");
		}
		return carta;
	}
	
	/*@   public normal_behavior
	  @	   requires   !cartas.isEmpty();
	  @ also
	  @   public exceptional_behavior
	  @ 	requires     !cartas.isEmpty();
	  @ 	signals_only CartaNotFoundException;
	  @*/
	private /*@ pure @*/ Carta getCartaParaCimaByValor(int valor) throws CartaNotFoundException{
		for (Carta carta: cartas) {
			if (carta.getValor() == valor && carta.isParaCima()) return carta;
		}
		throw new CartaNotFoundException("Carta não encontrada");
	}
	
	/**Puxa todas as cartas acima de uma carta de valor passado como parâmetro.
	 * @param valor		Valor da primeira carta do monte a ser movido
	 * @return Lista de cartas puxadas*/
	/*@ requires   1 <= valor && valor <= 13;
	  @ assignable this.cartas;
	  @ ensures    this.cartas.size() < \old(this.cartas.size());
	  @*/
	public ArrayList<Carta> puxarAPartirDeCarta(int valor){
		Carta primeira;
		try {
			primeira = getCartaParaCimaByValor(valor);
		} catch (CartaNotFoundException e) {
			primeira = null;
		}
		ArrayList<Carta> result = new ArrayList<>();
		
		if (primeira == null) return result;
		
		Carta carta = puxarCartaTopo();
		while (carta != null && carta.compareTo(primeira) != 0 ) {
			result.add(0,carta);
			carta = puxarCartaTopo();
		}
		
		result.add(0,primeira);
		return result;
	}
	
	/**Checar se Pilha está vazia.
	 * @return Booleano representando se Pilha está vazia*/
	public /*@ pure @*/ boolean isEmpty() {
		return cartas.isEmpty();
	}
	
	public  /*@ pure @*/ Carta[] getCartas() {
		Object[] obs = cartas.toArray();
		Carta[] cards = new Carta[obs.length];
		
		for (int i = 0; i < obs.length; i++) cards[i] = (Carta)obs[i];
			
		return cards;
	}
	
	public /*@ pure @*/ String toString() {
		StringBuilder sb = new StringBuilder();
		boolean first = true;
		for (Carta carta: cartas) {
			if (first) {
				sb.append(carta.toString());
				first = false;
			} else{ 
				sb.append(", ");
				sb.append(carta.toString());
			}
		}
		return sb.toString();
	}
}
