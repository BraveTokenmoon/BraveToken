// File: contracts/protocols/bep/BepLib.sol
//SPDX-License-Identifier: Unlicensed
pragma solidity >=0.6.8;
pragma experimental ABIEncoderV2;

interface IBEP20 {

    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */

library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != accountHash && codehash != 0x0);
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an BNB balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: weiValue }(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
contract Ownable is Context {
    address private _owner;
    address private _previousOwner;
    uint256 private _lockTime;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
    * @dev Leaves the contract without owner. It will not be possible to call
    * `onlyOwner` functions anymore. Can only be called by the current owner.
    *
    * NOTE: Renouncing ownership will leave the contract without an owner,
    * thereby removing any functionality that is only available to the owner.
    */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }

    function geUnlockTime() public view returns (uint256) {
        return _lockTime;
    }

    //Locks the contract for owner for the amount of time provided
    function lock(uint256 time) public virtual onlyOwner {
        _previousOwner = _owner;
        _owner = address(0);
        _lockTime = now + time;
        emit OwnershipTransferred(_owner, address(0));
    }

    //Unlocks the contract for owner when _lockTime is exceeds
    function unlock() public virtual {
        require(_previousOwner == msg.sender, "You don't have permission to unlock");
        require(now > _lockTime , "Contract is locked until 7 days");
        emit OwnershipTransferred(_owner, _previousOwner);
        _owner = _previousOwner;
    }
}

interface IPancakeFactory {
    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    function feeTo() external view returns (address);
    function feeToSetter() external view returns (address);

    function getPair(address tokenA, address tokenB) external view returns (address pair);
    function allPairs(uint) external view returns (address pair);
    function allPairsLength() external view returns (uint);

    function createPair(address tokenA, address tokenB) external returns (address pair);

    function setFeeTo(address) external;
    function setFeeToSetter(address) external;
}

interface IPancakePair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function price0CumulativeLast() external view returns (uint);
    function price1CumulativeLast() external view returns (uint);
    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);
    function burn(address to) external returns (uint amount0, uint amount1);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
    function skim(address to) external;
    function sync() external;

    function initialize(address, address) external;
}

interface IPancakeRouter01 {
    function factory() external pure returns (address);
    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB, uint liquidity);
    function addLiquidityETH(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external payable returns (uint amountToken, uint amountETH, uint liquidity);
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETH(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountToken, uint amountETH);
    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETHWithPermit(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountToken, uint amountETH);
    function swapExactTokensForTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapTokensForExactTokens(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapExactETHForTokens(uint amountOutMin, address[] calldata path, address to, uint deadline)
    external
    payable
    returns (uint[] memory amounts);
    function swapTokensForExactETH(uint amountOut, uint amountInMax, address[] calldata path, address to, uint deadline)
    external
    returns (uint[] memory amounts);
    function swapExactTokensForETH(uint amountIn, uint amountOutMin, address[] calldata path, address to, uint deadline)
    external
    returns (uint[] memory amounts);
    function swapETHForExactTokens(uint amountOut, address[] calldata path, address to, uint deadline)
    external
    payable
    returns (uint[] memory amounts);

    function quote(uint amountA, uint reserveA, uint reserveB) external pure returns (uint amountB);
    function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) external pure returns (uint amountOut);
    function getAmountIn(uint amountOut, uint reserveIn, uint reserveOut) external pure returns (uint amountIn);
    function getAmountsOut(uint amountIn, address[] calldata path) external view returns (uint[] memory amounts);
    function getAmountsIn(uint amountOut, address[] calldata path) external view returns (uint[] memory amounts);
}

interface IPancakeRouter02 is IPancakeRouter01 {
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountETH);
    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountETH);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable;
    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
}

library BraveCommon {
    using SafeMath for uint256;

    function random(uint256 from, uint256 to, uint256 salty) internal view returns (uint256) {
        uint256 seed = uint256(
            keccak256(
                abi.encodePacked(
                    block.timestamp + block.difficulty +
                    ((uint256(keccak256(abi.encodePacked(block.coinbase)))) / (block.timestamp)) +
                    block.gaslimit +
                    ((uint256(keccak256(abi.encodePacked(msg.sender)))) / (block.timestamp)) +
                    block.number +
                    salty
                )
            )
        );
        return seed.mod(to - from) + from;
    }

    function getTokenBNBPairAddress(IPancakeRouter02 router, address tokenAddress) internal view returns (address)
    {
        return IPancakeFactory(router.factory()).getPair(tokenAddress, router.WETH());     
    }
}

contract BraveToken is Context, IBEP20, Ownable {
    using SafeMath for uint256;
    using Address for address;

    mapping(address => uint256) private _tOwned;
    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _tTotal = 10000000000 * 10 ** 6 * 10 ** 9;

    string private _name = "BraveToken";
    string private _symbol = "Brave";
    uint8 private _decimals = 9;

    IPancakeRouter02 private pancakeRouter;
    BraveWhiteList private whiteList;

    constructor (
        address payable routerAddress,
        address whiteListAddress
    ) public {
        
        _tOwned[_msgSender()] = _tTotal.mul(94) / 100;
       
        _tOwned[salePool] = _tTotal.mul(5) / 100;
        
        _tOwned[addressAD] = _tTotal / 100;

        IPancakeRouter02 _pancakeRouter = IPancakeRouter02(routerAddress);
        // set the rest of the contract variables
        pancakeRouter = _pancakeRouter;
        whiteList = BraveWhiteList(whiteListAddress);

        
        updateRewardTime(salePool);
        _lotteryIncluded.push(salePool);
        _lotterySeek[salePool] = 7;

        lotteryTermsAmount.push(0);

        
        wonNumCurrent = whiteList.wonNum();
        claimLotteryNumberCurrent = whiteList.claimLotteryNumber();

        emit Transfer(address(0), _msgSender(), _tTotal);
    }

    function name() public view returns (string memory) {
        return _name;
    }

    function symbol() public view returns (string memory) {
        return _symbol;
    }

    function decimals() public view returns (uint8) {
        return _decimals;
    }

    function totalSupply() public view override returns (uint256) {
        return _tTotal;
    }

    function balanceOf(address account) public view override returns (uint256) {
        return _tOwned[account];
    }

    function transfer(address recipient, uint256 amount) public override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    function allowance(address owner, address spender) public view override returns (uint256) {
        return _allowances[owner][spender];
    }

    function approve(address spender, uint256 amount) public override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    function transferFrom(address sender, address recipient, uint256 amount) public override returns (bool) {
        _transfer(sender, recipient, amount);
        //_approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "BEP20: transfer amount exceeds allowance"));
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount));
        return true;
    }

    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
        return true;
    }

    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        //_approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue, "BEP20: decreased allowance below zero"));
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue));
        return true;
    }

    //to receive BNB from pancakeRouter when swapping
    receive() external payable {}

    function _approve(address owner, address spender, uint256 amount) private {
        //require(owner != address(0), "BEP20: approve from the zero address");
        //require(spender != address(0), "BEP20: approve to the zero address");
        require(owner != address(0));
        require(spender != address(0));

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    function _transfer(
        address from,
        address to,
        uint256 amount
    ) private {
        //require(from != address(0), "ERC20: transfer from the zero address");
        //require(to != address(0), "ERC20: transfer to the zero address");
        //require(amount > 0, "Transfer amount must be greater than zero");

        require(from != address(0));
        require(to != address(0));
        require(amount > 0);

        
        address pancakePair = BraveCommon.getTokenBNBPairAddress(pancakeRouter, address(this));

        
        if(from == pancakePair) {
            if(to == address(pancakeRouter)) {
                
                _transferStandard(from, to, amount);
            }else {
                
                require(to == address(addressAD) && swapUnlock);
                
                uint256 restAmount = amount.sub(getBurnTxFee(from, amount));
                
                if(!isAccountActive[tx.origin]) {
                    isAccountActive[tx.origin] = true;
                    activeAccountsNum += 1;
                }
                includeLotteryAccount(tx.origin, restAmount);
                _transferStandard(from, tx.origin, restAmount);
                updateRewardTime(tx.origin);
                swapUnlock = false;
            }
        }else if(to == pancakePair) {
           
            if(from != owner()) {
                require(from == address(this));
            }
            _transferStandard(from, to, amount);
        }else {
            
            if(!isAccountActive[to]) {
                isAccountActive[to] = true;
                activeAccountsNum += 1;
            }
            if(whiteList.whiteListActive(from) == true || whiteList.whiteListActive(to) == true) {
                _transferStandard(from, to, amount);
            }else {
                swapBraveCtoC(from, to, amount);
                updateRewardTime(from);
                updateRewardTime(to);
            }
        }
    }

    function lotteryOpen(uint256 amount) private {
        address luckyAddress;
        claimLotteryCount += 1;
        if(_lotteryIncluded.length > 0) {
            for(uint256 i; i < wonNumCurrent; i++) {
                luckyAddress = _lotteryIncluded[BraveCommon.random(0, _lotteryIncluded.length, amount)];
                if(accountLotteryHistory[luckyAddress][lotteryTerm] == 0) {
                    accountLotteryTerms[luckyAddress].push(lotteryTerm);
                }
                accountLotteryHistory[luckyAddress][lotteryTerm] += 1;
            }
        }
        
        if(claimLotteryCount >= claimLotteryNumberCurrent) {
            lotteryTermsAmount.pop();
            lotteryTermsAmount.push(termLotteryBNB.div(claimLotteryNumberCurrent.mul(wonNumCurrent)));
            lotteryTerm += 1;
            lotteryTermsAmount.push(0);
            claimLotteryCount = 0;
            termLotteryBNB = 0;
        
            wonNumCurrent = whiteList.wonNum();
            claimLotteryNumberCurrent = whiteList.claimLotteryNumber();
        }
    }

    function _transferStandard(address sender, address recipient, uint256 amount) private {
        _tOwned[sender] = _tOwned[sender].sub(amount);
        _tOwned[recipient] = _tOwned[recipient].add(amount);
        emit Transfer(sender, recipient, amount);
    }

  
    bool private swapUnlock;

   
    mapping(address => bool) private isAccountActive;
    uint256 public activeAccountsNum;

    
    address private salePool = 0x01DdADFc46b0BD4FBe72d5619Dc54239108eC506;
    address private addressAD = 0x3A9f4021365c6117bDfE0095604959931D1fA6e6;

  
    uint256 public lotteryPoolBNB;
    uint256 public rewardPoolBNB;


    uint256 public claimLotteryCount = 0;
    uint256 public getLotteryAmount = 10**12 * 10 ** 9;
  
    uint256 private termLotteryBNB;
    address[] private _lotteryIncluded;
    mapping(address => uint256) public _lotterySeek;
    uint256 public lotteryTerm;
    uint256[] public lotteryTermsAmount;
    mapping(address => mapping(uint256 => uint256)) public accountLotteryHistory;

    mapping(address => uint256[]) public accountLotteryTerms;
 
    uint256 public claimLotteryNumberCurrent;
    uint256 public wonNumCurrent;


    mapping (address => uint256) public nextRewardTime;


    uint256 public buyLimitPerDay = 10;
    uint256 private amountLimitPerTime = 4 * 10**17;


    mapping(address => uint256) public accountBuyNumState;
    mapping(address => uint256) private accountBuyDayState;

    function excludeLotteryAccount(address sender, uint256 amount) private {

        if(_tOwned[sender] >= getLotteryAmount && _tOwned[sender].sub(amount) < getLotteryAmount) {
            _lotteryIncluded[_lotterySeek[sender]-7] = _lotteryIncluded[_lotteryIncluded.length-1];
            _lotterySeek[_lotteryIncluded[_lotteryIncluded.length-1]] = _lotterySeek[sender];
            _lotterySeek[sender] = 0;
            _lotteryIncluded.pop();
        }
    }

 
    function includeLotteryAccount(address recipient, uint256 amount) private {

        if(_tOwned[recipient] < getLotteryAmount && _tOwned[recipient].add(amount) >= getLotteryAmount) {
            _lotteryIncluded.push(recipient);
            _lotterySeek[recipient] = _lotteryIncluded.length-1+7;
        }
    }


    function includeLotteryAccountForce() public {
        require(_lotterySeek[msg.sender] == 0 && _tOwned[msg.sender] >= getLotteryAmount);
        _lotteryIncluded.push(msg.sender);
        _lotterySeek[msg.sender] = _lotteryIncluded.length-1+7;
    }


    function claimReward() public {
        require(nextRewardTime[msg.sender] != 0 && block.timestamp >= nextRewardTime[msg.sender]);

        uint256 reward = getRewardAmount(msg.sender);
        rewardPoolBNB = rewardPoolBNB.sub(reward);
        (bool sent,) = msg.sender.call{value : reward}("");
        require(sent);
        updateRewardTime(msg.sender);
    }


    function claimLottery() public {
        uint256 reward;
        uint256 term;
        uint256 times = getLotteryLength(msg.sender);
        uint256 temp = accountLotteryTerms[msg.sender][times-1];
        for(uint256 i; i < times; i++) {
            term = accountLotteryTerms[msg.sender][times-i-1];
            reward += lotteryTermsAmount[term].mul(accountLotteryHistory[msg.sender][term]);
            accountLotteryTerms[msg.sender].pop();
        }
        if(lotteryTermsAmount[temp] == 0) {
            accountLotteryTerms[msg.sender].push(temp);
        }
        require(reward > 0);
        lotteryPoolBNB = lotteryPoolBNB.sub(reward);
        (bool sent,) = msg.sender.call{value : reward}("");
        require(sent);
    }

    function getLotteryLength(address account) public view returns (uint256) {
        return accountLotteryTerms[account].length;
    }

    function updateRewardTime(address account) private {
        nextRewardTime[account] = block.timestamp + whiteList.rewardLimitPeriod();
    }

 
    function updateBuyState(address account) private {
        uint256 getTodayCount = block.timestamp / 86400;
        if(accountBuyDayState[account] != getTodayCount) {
            accountBuyDayState[account] = getTodayCount;
            accountBuyNumState[account] = 0;
        }
    }


    function getBurnTxFee(address from, uint256 amount) private returns (uint256) {
        uint256 burnFee = amount.mul(4) / 100;
        _transferStandard(from, address(0x000000000000000000000000000000000000dEaD), burnFee);
        return burnFee;
    }


    function paySwapTxFee(uint256 amount) private {

        uint256 txFeeBase = amount / 6;
        uint256 restFee = amount.sub(txFeeBase.mul(3));
  
        lotteryPoolBNB += txFeeBase.mul(2);
        termLotteryBNB += txFeeBase.mul(2);

        rewardPoolBNB += restFee;

        (bool sent,) = salePool.call{value : txFeeBase}("");
        require(sent);
    }


    function setBuyLimitPerDay(uint256 num) public {
        require(tx.origin == owner());
        buyLimitPerDay = num;
    }

    function setAmountLimitPerTime(uint256 amount) public {
        require(tx.origin == owner());
        amountLimitPerTime = amount;
    }


    function setGetLotteryAmount(uint256 amount) public {
        require(tx.origin == owner());
        getLotteryAmount = amount;
    }


    function swapBNBForBrave() public payable {

        swapUnlock = true;


        uint256 bnbCanSwap = msg.value;


        updateBuyState(msg.sender);

        require((bnbCanSwap <= amountLimitPerTime) && (accountBuyNumState[msg.sender] < buyLimitPerDay));

        accountBuyNumState[msg.sender] += 1;


        uint256 swapTxFee = bnbCanSwap.mul(6) / 100;
        uint256 bnbSwap = bnbCanSwap.sub(swapTxFee);
        paySwapTxFee(swapTxFee);


        address[] memory path = new address[](2);
        path[0] = pancakeRouter.WETH();
        path[1] = address(this);
        pancakeRouter.swapExactETHForTokensSupportingFeeOnTransferTokens{value: bnbSwap}(
            0,
            path,
            address(addressAD),
            block.timestamp
        );


        lotteryOpen(msg.value);
    }

    function swapTokenForBrave(uint256 amount, address tokenAddress) public {   

        swapUnlock = true;


        IBEP20(tokenAddress).transferFrom(msg.sender, address(this), amount);
        IBEP20(tokenAddress).approve(address(pancakeRouter), amount);

        address[] memory path = new address[](2);
        path[0] = tokenAddress;
        path[1] = pancakeRouter.WETH();


        uint256[] memory bnbCanSwap = pancakeRouter.getAmountsOut(amount, path);


        updateBuyState(msg.sender);

        require((bnbCanSwap[1] <= amountLimitPerTime) && (accountBuyNumState[msg.sender] < buyLimitPerDay));

        accountBuyNumState[msg.sender] += 1;


        pancakeRouter.swapExactTokensForETHSupportingFeeOnTransferTokens(
            amount,
            0, // accept any amount of BNB
            path,
            address(this),
            block.timestamp
        );


        uint256 swapTxFee = bnbCanSwap[1].mul(6) / 100;
        uint256 bnbSwap = bnbCanSwap[1].sub(swapTxFee);
        paySwapTxFee(swapTxFee);


        path[0] = pancakeRouter.WETH();
        path[1] = address(this);
        pancakeRouter.swapExactETHForTokensSupportingFeeOnTransferTokens{value: bnbSwap}(
            0,
            path,
            address(addressAD),
            block.timestamp
        );


        lotteryOpen(amount);
    }


    function swapBraveForToken(uint256 amount, address tokenAddress) public {

        excludeLotteryAccount(msg.sender, amount);

        updateRewardTime(msg.sender);


        _transferStandard(msg.sender, address(this), amount);


        uint256 restAmount = amount.sub(getBurnTxFee(address(this), amount));
        
        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = pancakeRouter.WETH();


        uint256[] memory bnbCanSwap = pancakeRouter.getAmountsOut(restAmount, path);


        _approve(address(this), address(pancakeRouter), restAmount);


        pancakeRouter.swapExactTokensForETHSupportingFeeOnTransferTokens(
            restAmount,
            0, // accept any amount of BNB
            path,
            address(this),
            block.timestamp
        );


        uint256 swapTxFee = bnbCanSwap[1].mul(6) / 100;
        uint256 bnbSwap = bnbCanSwap[1].sub(swapTxFee);
        paySwapTxFee(swapTxFee);

        if(tokenAddress == address(0)) {
  
            (bool sent, ) = tx.origin.call{ value: bnbSwap }("");
            require(sent);
        }else {

            path[0] = pancakeRouter.WETH();
            path[1] = tokenAddress;
            pancakeRouter.swapExactETHForTokensSupportingFeeOnTransferTokens{value: bnbSwap}(
                0,
                path,
                tx.origin,
                block.timestamp
            );
        }


        lotteryOpen(amount);   
    }


    function swapBraveCtoC(address from, address to, uint256 amount) private {

        excludeLotteryAccount(from, amount);


        uint256 burnAmount = getBurnTxFee(from, amount);

        uint256 swapAmount = amount.mul(6) / 100;
        uint256 restAmount = amount.sub(swapAmount).sub(burnAmount);

        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = pancakeRouter.WETH();


        uint256[] memory bnbCanSwap = pancakeRouter.getAmountsOut(swapAmount, path);


        _transferStandard(from, address(this), swapAmount);


        _approve(address(this), address(pancakeRouter), swapAmount);

        pancakeRouter.swapExactTokensForETHSupportingFeeOnTransferTokens(
            swapAmount,
            0, // accept any amount of BNB
            path,
            address(this),
            block.timestamp
        );


        paySwapTxFee(bnbCanSwap[1]);


        if(to != address(0x000000000000000000000000000000000000dEaD)) {
            includeLotteryAccount(to, restAmount);
        }
        _transferStandard(from, to, restAmount);


        lotteryOpen(amount);
    }


    function getPairCondition() public view returns (uint256 pairBNBAmount, uint256 pairTokenAmount, uint256 tokenTotal) {

        address pancakePair = BraveCommon.getTokenBNBPairAddress(pancakeRouter, address(this));
        if(pancakePair == address(0)) {
            pairBNBAmount = 0;
            pairTokenAmount = 0;
        }else {
            pairBNBAmount = IBEP20(pancakeRouter.WETH()).balanceOf(pancakePair);
            pairTokenAmount = _tOwned[pancakePair];
        }
        tokenTotal = _tTotal;
    }



    function getRewardAmount(address account) public view returns (uint256) {
        return rewardPoolBNB.mul(whiteList.discount()).div(100).mul(_tOwned[account]).div(getCurrency());
    }


    function getCurrency() public view returns (uint256) {

        address pancakePair = BraveCommon.getTokenBNBPairAddress(pancakeRouter, address(this));

        return _tTotal.sub(_tOwned[address(0x000000000000000000000000000000000000dEaD)]).sub(_tOwned[pancakePair]);
    }
}

contract BraveWhiteList is Ownable {
    using SafeMath for uint256;
    using Address for address;

    address[] public whiteList;

    mapping(address => bool) public whiteListActive;

    uint256 public discount = 80;
    uint256 public claimLotteryNumber = 1000;
    uint256 public rewardLimitPeriod = 3 days; 
    uint256 public wonNum = 1;

    constructor () public {
        whiteList.push(msg.sender);
        whiteList.push(0x01DdADFc46b0BD4FBe72d5619Dc54239108eC506);
        whiteList.push(0x3A9f4021365c6117bDfE0095604959931D1fA6e6);
        whiteListActive[msg.sender] = true;
        whiteListActive[0x01DdADFc46b0BD4FBe72d5619Dc54239108eC506] = true;
        whiteListActive[0x3A9f4021365c6117bDfE0095604959931D1fA6e6] = true;
    }

    function getLotteryTermWonNum() public view returns(uint256) {
        return claimLotteryNumber.mul(wonNum);
    }

    function setWonNum(uint256 num) public {
        require(tx.origin == owner() && num >= 1);
        wonNum = num;
    }

    function setClaimLotteryNumber(uint256 num) public {
        require(tx.origin == owner());
        claimLotteryNumber = num;
    }

    function setRewardLimitPeriod(uint256 time) public {
        require(tx.origin == owner());
        rewardLimitPeriod = time;
    }

    function setDiscount(uint256 rate) public {
        require(tx.origin == owner() && rate <= 100);
        discount = rate;
    }

    function addWhiteList(address contractAddress) public onlyOwner {
        whiteList.push(contractAddress);
        whiteListActive[contractAddress] = true;
    }

    function removeWhiteList(address contractAddress) public onlyOwner {
        for(uint i; i < whiteList.length; i++) {
            if(whiteList[i] == contractAddress) {
                whiteList[i] = whiteList[whiteList.length-1];
                whiteList.pop();
                whiteListActive[contractAddress] = false;
                break;
            }
        }
    }
}

contract BraveTokenView {
    using SafeMath for uint256;
    using Address for address;

    IPancakeRouter02 public immutable pancakeRouter;

    constructor (
        address payable routerAddress
    ) public {
        IPancakeRouter02 _pancakeRouter = IPancakeRouter02(routerAddress);
        pancakeRouter = _pancakeRouter;
    }
    
    function getPancakeBNBTokenPair(address tokenAddress) public view returns (address) {
        return BraveCommon.getTokenBNBPairAddress(pancakeRouter, tokenAddress);
    }

    function getBNBTokenPairAmounts(address tokenAddress) public view returns (address, uint256, address, uint256) {
        address pancakePair = getPancakeBNBTokenPair(tokenAddress);
        (uint256 reserve0, uint256 reserve1,) = IPancakePair(pancakePair).getReserves();
        address token0Address = IPancakePair(pancakePair).token0();
        address token1Address = IPancakePair(pancakePair).token1();
        return (token0Address, reserve0, token1Address, reserve1);
    }

    function getNowTimeStamp() public view returns (uint256) {
        return block.timestamp;
    }

    function getAddressLotteryBalance(address account, BraveToken tokenAddress) public view returns (uint256 reward) {
        uint256 term;
        uint256 times = tokenAddress.getLotteryLength(account);
        if(times == 0) {
            return 0;
        }
        for(uint256 i; i < times; i++) {
            term = tokenAddress.accountLotteryTerms(account, times-i-1);
            reward += tokenAddress.lotteryTermsAmount(term).mul(tokenAddress.accountLotteryHistory(account, term));
        }
    }
}
