package model;

import util.Carta;
import util.Naipe;

/**
 * Representa uma Pilha de Descarte do jogo Paciencia.
 * Eh a pilha que possui todas as cartas que sao puxadas
 * do Estoque.
 **/
public class Descarte extends Pilha {
	public Descarte (){
		super();
	}
	
	@Override
	protected /*@ pure @*/ boolean verificarCarta(Carta carta) {
		return false;
	}
	
	public static void main(String[] args) {
		Descarte descarte = new Descarte();
		System.out.println(descarte.verificarCarta(new Carta(1, Naipe.ESPADA)));
	}
}