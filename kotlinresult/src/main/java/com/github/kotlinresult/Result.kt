package com.github.kotlinresult

/**
 * A discriminated union that encapsulates successful outcome with a value of type [T]
 * or a failure with an arbitrary [Throwable] exception.
 */
sealed class Result<out T> {
  data class Success<T>(val value: T) : Result<T>()
  data class Failure(val exception: Throwable) : Result<Nothing>()

  companion object {
    fun <T> success(value: T): Result<T> =
        Success(value)

    fun failure(exception: Throwable): Result<Nothing> =
        Failure(exception)
  }
}

/**
 * Returns the the result of [onSuccess] for encapsulated value if this instance represents is [Result.Success]
 * or the result of [onFailure] function for encapsulated exception if it is [Result.Error].
 *
 * Note, that an exception thrown by [onSuccess] or by [onFailure] function is rethrown by this function.
 */
inline fun <R, T> Result<T>.fold(
    onSuccess: (data: T) -> R,
    onFailure: (exception: Throwable) -> R
): R {
  return when (this) {
    is Result.Success -> onSuccess(value)
    is Result.Failure -> onFailure(exception)
  }
}

/**
 * Returns the result of [onSuccess] for encapsulated value with `this` as its receiver if this instance represents is [Result.Success]
 * or the result of [onFailure] function for an encapsulated exception with `this` as its receiver if it is [Result.Error].
 *
 *Note, that an exception thrown by [onSuccess] or by [onFailure] function is rethrown by this function.
 */
inline fun <T, R> Result<T>.foldExtracted(
    onSuccess: T.() -> R,
    onFailure: Throwable.() -> R
): R {
  return when (this) {
    is Result.Success -> onSuccess(value)
    is Result.Failure -> onFailure(exception)
  }
}

/**
 * Returns the [value][Result.Success.data] if this [Result] is [Result.Success], otherwise `null`.
 */
inline fun <T> Result<T>.getOrNull(): T? {
  return when (this) {
    is Result.Success -> value
    is Result.Failure -> null
  }
}

/**
 * Returns the encapsulated exception if this instance represents [failure][Result.Error] or `null`
 * if it is [success][Result.Success].
 *
 * This function is shorthand for `fold(onSuccess = { null }, onFailure = { it })` (see [fold]).
 */
inline fun <E> Result<E>.exceptionOrNull(): Throwable? =
    when (this) {
      is Result.Failure -> exception
      else -> null
    }

/**
 * Returns the encapsulated value if this instance represents [success][Result.isSuccess] or the
 * [defaultValue] if it is [failure][Result.isFailure].
 *
 * This function is shorthand for `getOrElse { defaultValue }` (see [getOrElse]).
 */
inline fun <R, T : R> Result<T>.getOrDefault(defaultValue: R): R {
  return when (this) {
    is Result.Success -> value
    is Result.Failure -> defaultValue
  }
}

/**
 * Calls the specified function [block] with `this` value as its receiver and returns its encapsulated result
 * if invocation was successful, catching and encapsulating any thrown exception as a Result.failure.
 */
inline fun <T, R> T.resultFrom(block: T.() -> R): Result<R> {
  return try {
    Result.success(block())
  } catch (e: Throwable) {
    Result.failure(e)
  }
}

/**
 * Call a function and wrap the result in a Result, catching any Exception and returning it as Result.failure value.
 */
inline fun <T> resultFrom(block: () -> T): Result<T> {
  return try {
    Result.success(block())
  } catch (e: Throwable) {
    Result.failure(e)
  }
}


/**
 * Transformation
 */

/**
 * Returns the encapsulated result of the given [transform] function applied to encapsulated value
 * if this instance represents [success][Result.Success] or the
 * original encapsulated exception if it is [failure][Result.Failure].
 *
 * Note, that an exception thrown by [transform] function is rethrown by this function.
 * See [mapCatching] for an alternative that encapsulates exceptions.
 */
inline fun <R, T> Result<T>.map(transform: (value: T) -> R): Result<R> {
  return when (this) {
    is Result.Success -> Result.success(
        transform(value))
    is Result.Failure -> Result.failure(
        exception)
  }
}

/**
 * Returns the encapsulated result of the given [transform] function applied to encapsulated value
 * if this instance represents [success][Result.Success] or the
 * original encapsulated exception if it is [failure][Result.Failure].
 *
 * Any exception thrown by [transform] function is caught, encapsulated as a failure and returned by this function.
 * See [map] for an alternative that rethrows exceptions.
 */
inline fun <R, T> Result<T>.mapCatching(transform: (value: T) -> R): Result<R> {
  return try {
    when (this) {
      is Result.Success -> Result.success(
          transform(value))
      is Result.Failure -> Result.failure(
          exception)
    }
  } catch (e: Throwable) {
    Result.failure(e)
  }
}

/**
 * Maps this [Result<T>][Result] to [Result<R>][Result] by either applying the [transform]
 * function if this [Result] is [Result.Success], or returning this [Result.Failure].
 */
inline fun <R, T> Result<T>.flatMap(transform: (value: T) -> Result<R>): Result<R> {
  return try {
    when (this) {
      is Result.Success -> transform(value)
      is Result.Failure -> this
    }
  } catch (e: Throwable) {
    Result.failure(e)
  }
}

/**
 * Maps this [Result<T>][Result] to [Result<T>][Result] by either applying the [transform]
 * function to the [error][Result.failure] if this [Result] is [Result.Failure], or returning this [Result.Success].
 */
inline fun <R, T : R> Result<T>.mapError(
    transform: (exception: Throwable) -> Throwable
): Result<R> {
  return when (this) {
    is Result.Success -> this
    is Result.Failure -> Result.failure(
        transform(exception))
  }
}

/**
 * Maps this [Result<T>][Result] to [Result<T>][Result] by either applying the [transform]
 * function to the [error][Result.failure] if this [Result] is [Result.Failure], or returning this [Result.Success].
 */
inline fun <T> Result<T>.flatMapError(
    transform: (exception: Throwable) -> Result<T>
): Result<T> {
  return when (this) {
    is Result.Success -> this
    is Result.Failure -> transform(exception)
  }
}

/**
 * Returns the encapsulated result of the given [transform] function applied to encapsulated exception
 * if this instance represents [failure][Result.Failure] or the
 * original encapsulated value if it is [success][Result.Success].
 *
 * Note, that an exception thrown by [transform] function is rethrown by this function.
 * See [recoverCatching] for an alternative that encapsulates exceptions.
 */
inline fun <R, T : R> Result<T>.recover(transform: (exception: Throwable) -> R): Result<R> {
  return when (this) {
    is Result.Success -> this
    is Result.Failure -> Result.success(
        transform(exception))
  }
}

/**
 * Returns the encapsulated result of the given [transform] function applied to encapsulated exception
 * if this instance represents [failure][Result.Failure] or the
 * original encapsulated value if it is [success][Result.Success].
 *
 * Any exception thrown by [transform] function is caught, encapsulated as a failure and returned by this function.
 * See [recover] for an alternative that rethrows exceptions.
 */
inline fun <R, T : R> Result<T>.recoverCatching(transform: (exception: Throwable) -> R): Result<R> {
  return try {
    when (this) {
      is Result.Success -> this
      is Result.Failure -> Result.success(
          transform(exception))
    }
  } catch (e: Throwable) {
    Result.failure(e)
  }
}

/**
 * "peek" onto value/exception and pipe
 */

/**
 * Performs the given [action] on encapsulated exception if this instance represents [failure][Result.Failure].
 * Returns the original `Result` unchanged.
 */
inline fun <T> Result<T>.onFailure(action: (exception: Throwable) -> Unit): Result<T> {
  exceptionOrNull()?.let { action(it) }
  return this
}

/**
 * Performs the given [action] on encapsulated value if this instance represents [success][Result.Success].
 * Returns the original `Result` unchanged.
 */
inline fun <T> Result<T>.onSuccess(action: (value: T) -> Unit): Result<T> {
  if (this is Result.Success) action(value)
  return this
}