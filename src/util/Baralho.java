package util;

import java.util.ArrayList;
import java.util.Collections;


public class Baralho {
	private /*@ spec_public @*/ ArrayList<Carta> cartas;

	/*@ assignable this.cartas;
	  @ ensures    this.cartas.size() == 52;
	  @*/
	public Baralho () {
		cartas = new ArrayList<>();
		
		for (Naipe naipe: Naipe.values()) {
			for (int val = Carta.AS; val <= Carta.K; val++) {
				cartas.add(new Carta(val,naipe));
			}
		}
	}
	
	/*@ assignable this.cartas; 
	  @*/
	public Baralho (boolean embaralhar) {
		this();
		if (embaralhar) {
			Collections.shuffle(cartas);
		}
	}
	
	/*@ requires   0 <= qtd;
	  @ assignable this.cartas;
	  @ ensures    this.cartas.size() == (\old(this.cartas.size()) - qtd)  || this.isEmpty(); 
	  @*/
	public ArrayList<Carta> puxarCartas(int qtd) {
		ArrayList<Carta> cartasPuxadas = new ArrayList<>();
		
		while (!isEmpty() && qtd > 0) {
			Carta cartaPuxada = cartas.remove(cartas.size()-1);
			cartasPuxadas.add(cartaPuxada);
			qtd--;
		}
		
		return cartasPuxadas;
	}


	/*@ assignable this.cartas;
	  @ ensures    this.cartas.size() == 0;
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
	
	public static void main(String[] args) {
		Baralho b = new Baralho(true);
		System.out.println(b.puxarCartas(40));
		System.out.println(b.puxarTodasAsCartas());
		System.out.println(b.isEmpty());
	}
}
