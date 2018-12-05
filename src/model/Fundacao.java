package model;


import exception.PilhaVaziaException;
import util.Carta;


public class Fundacao extends Pilha {

	public Fundacao() {
		super();
	}
	
	@Override
	protected boolean verificarCarta(Carta carta) {
		if (!carta.isParaCima()) return false;
		
		if (isEmpty()) {
			if (carta.getValor() == Carta.MENOR_VALOR) return true;
			return false;
		}
		
		Carta topo = null;
		try {
			topo = cartaTopo();
		} catch (PilhaVaziaException e) {
			System.out.println("Não há carta no topo");
		}
		
		if (topo.getValor()+1 == carta.getValor() && topo.getNaipe() == carta.getNaipe())
			return true;
		
		return false;
	}

}
