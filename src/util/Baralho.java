package util;

import java.util.ArrayList;
import java.util.Collections;


public class Baralho {

	private /*@ spec_public @*/ ArrayList<Carta> cartas;

	public Baralho () {
		cartas = new ArrayList<>();
		
		for (Naipe naipe: Naipe.values()) {
			for (int val = Carta.AS; val <= Carta.K; val++) {
				cartas.add(new Carta(val,naipe));
			}
		}
	}
	
	public Baralho (boolean embaralhar) {
		this();
		if (embaralhar) {
			Collections.shuffle(cartas);
		}
	}

	public ArrayList<Carta> puxarCartas(int qtd) {
		ArrayList<Carta> cartasPuxadas = new ArrayList<>();
		
		while (!isEmpty() && qtd > 0) {
			Carta cartaPuxada = cartas.remove(cartas.size()-1);
			cartasPuxadas.add(cartaPuxada);
			qtd--;
		}
		
		return cartasPuxadas;
	}


	/*@
	  @ assignable this.cartas, cartasPuxadas;
	  @ ensures this.cartas.size() == 0;
	  @ ensures cartasPuxadas.equals(\old(this.cartas));
	  @*/
	public ArrayList<Carta> puxarTodasAsCartas() {
		ArrayList<Carta> cartasPuxadas = new ArrayList<>();
		
		cartasPuxadas.addAll(cartas);
		Collections.reverse(cartasPuxadas);
		
		cartas.clear();
		
		return cartasPuxadas;
	}
	
	public /*@ pure @*/ boolean isEmpty() {
		return cartas.isEmpty();
	}
}
