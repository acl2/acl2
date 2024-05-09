import org.bouncycastle.crypto.params.KeyParameter;
import org.bouncycastle.crypto.engines.AESLightEngine;

public class AESEncryptLightDriver {

    // Encrypt IN using KEY, putting the result into OUT.
    public static byte[] driver(byte[] key, byte [] in, byte [] out) {
        KeyParameter params = new KeyParameter(key);
        AESLightEngine engine = new AESLightEngine();
        engine.init(true, params); // true means encrypt, not decrypt
        engine.processBlock(in, 0, out, 0);
        return out;
    }

}
