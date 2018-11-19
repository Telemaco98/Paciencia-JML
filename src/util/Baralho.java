package util;

import java.util.ArrayList;
import java.util.Collections;


public class Baralho {

	private ArrayList<Carta> cartas;

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

	public ArrayList<Carta> puxarTodasAsCartas() {
		ArrayList<Carta> cartasPuxadas = new ArrayList<>();
		
		cartasPuxadas.addAll(cartas);
		Collections.reverse(cartasPuxadas);
		cartas.clear();
		
		return cartasPuxadas;
	}

	public boolean isEmpty() {
		return cartas.isEmpty();
	}
}
